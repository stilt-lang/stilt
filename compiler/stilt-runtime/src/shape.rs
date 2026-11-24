//! Shapes: how a type's values are held, which compiled code passes as a type parameter's
//! witness and which a list keeps for its elements (`stilt_mir::shape` builds them).
//!
//! A shape is one word. Its lowest bit tells whether the one word that holds a value where a
//! type parameter stands is a heap word: the value's own word, or for a value of several words,
//! its box. The rest tells how a list holds the values as its elements: their size in bytes,
//! which is the width of a scalar narrower than a word, 8 for a value of one word, and 8 per
//! word for a value held inline, with which of those words are heap words, and whether a
//! narrow scalar's reads extend its sign. The shape of a value of more than [`MASK_WORDS`]
//! words points instead to a description of its words ([`Large`]), which
//! [`stilt_rt_large_shape`] makes once for each and keeps while the program runs.

use std::collections::HashMap;
use std::sync::{Mutex, PoisonError};

use crate::layout::{
    MASK_WORDS, SHAPE_HEAP, SHAPE_LARGE, SHAPE_MASK_SHIFT, SHAPE_SIGNED, SHAPE_SIZE_BITS,
    SHAPE_SIZE_SHIFT,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Shape(pub(crate) u64);

/// The words of a value of more than [`MASK_WORDS`] words: how many, and the masks of its heap
/// words, word `i`'s at bit `i % 64` of mask `i / 64`.
#[derive(Debug)]
pub(crate) struct Large {
    words: usize,
    masks: Box<[u64]>,
}

impl Shape {
    /// The shape of a value of one word, a heap word if `heap` is set.
    pub(crate) const fn word(heap: bool) -> Self {
        let heap = heap as u64;
        Self((heap * SHAPE_HEAP) | (8 << SHAPE_SIZE_SHIFT) | (heap << SHAPE_MASK_SHIFT))
    }

    /// The shape of an unsigned scalar of `bytes` bytes, such as a `u8`.
    pub(crate) const fn unsigned(bytes: u64) -> Self {
        Self(bytes << SHAPE_SIZE_SHIFT)
    }

    /// The description of the words of a value of more than [`MASK_WORDS`] words.
    fn large(self) -> Option<&'static Large> {
        if self.0 & SHAPE_LARGE != SHAPE_LARGE {
            return None;
        }
        let at = (self.0 >> SHAPE_MASK_SHIFT) as *const Large;
        // SAFETY: a shape with these low bits is made by `stilt_rt_large_shape`, which points
        // it to a description that it keeps while the program runs.
        Some(unsafe { &*at })
    }

    /// Whether the word that holds a value where a type parameter stands is a heap word.
    pub(crate) const fn heap(self) -> bool {
        self.0 & SHAPE_HEAP != 0
    }

    /// The size of an element in bytes.
    pub(crate) fn size(self) -> usize {
        match self.large() {
            Some(l) => 8 * l.words,
            None => (self.0 >> SHAPE_SIZE_SHIFT & SHAPE_SIZE_BITS) as usize,
        }
    }

    /// Whether an element is a scalar narrower than a word.
    pub(crate) fn packed(self) -> bool {
        self.size() < 8
    }

    /// Whether a packed scalar's reads extend its sign.
    pub(crate) const fn signed(self) -> bool {
        self.0 & SHAPE_SIGNED != 0
    }

    /// The number of words of an element held inline: 1 for a value of one word or a packed
    /// scalar.
    pub(crate) fn words(self) -> usize {
        self.size().div_ceil(8)
    }

    /// Whether word `i` of an element is a heap word.
    pub(crate) fn heap_word(self, i: usize) -> bool {
        self.mask(i / 64) >> (i % 64) & 1 == 1
    }

    /// Mask `j` of an element's heap words, word `64 * j + k`'s at bit `k`.
    pub(crate) fn mask(self, j: usize) -> u64 {
        match self.large() {
            Some(l) => l.masks.get(j).copied().unwrap_or(0),
            None if j == 0 => self.0 >> SHAPE_MASK_SHIFT,
            None => 0,
        }
    }

    /// Whether some word of an element is a heap word.
    pub(crate) fn counted(self) -> bool {
        match self.large() {
            Some(l) => l.masks.iter().any(|&m| m != 0),
            None => self.0 >> SHAPE_MASK_SHIFT != 0,
        }
    }
}

/// The descriptions that large shapes point to, by their masks, made once each.
static LARGE: Mutex<Option<HashMap<Box<[u64]>, usize>>> = Mutex::new(None);

/// The shape of a value of more than [`MASK_WORDS`] words, of which those whose words at
/// `heap` have their lowest bit set are heap words: compiled code passes a scalar 0, a heap
/// word 1, and for a word of a type parameter, its witness.
///
/// # Safety
///
/// `heap` points to `n` words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_large_shape(heap: u64, n: u64) -> u64 {
    let heap = heap as usize as *const u64;
    let words = usize::try_from(n).expect("an element of under 2^64 words");
    // SAFETY: the caller guarantees the words.
    let heap = unsafe { std::slice::from_raw_parts(heap, words) };
    let mut masks = vec![0u64; words.div_ceil(64)];
    for (i, w) in heap.iter().enumerate() {
        masks[i / 64] |= (w & 1) << (i % 64);
    }
    large(masks, words)
}

/// The shape of a value made of parts, as an array held in memory is its elements
/// (generics.large-arrays): `parts` holds `n` pairs, each a number of values and their shape, the
/// values of each part one after the other.
///
/// # Safety
///
/// `parts` points to `2 * n` words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_shape_parts(parts: u64, n: u64) -> u64 {
    let parts = parts as usize as *const u64;
    let n = usize::try_from(n).expect("under 2^63 parts");
    // SAFETY: the caller guarantees the words.
    let parts = unsafe { std::slice::from_raw_parts(parts, 2 * n) };
    let pairs = || parts.chunks(2).map(|p| (p[0] as usize, Shape(p[1])));
    let words: usize = pairs().map(|(count, s)| count * s.words()).sum();
    let mut masks = vec![0u64; words.div_ceil(64)];
    let mut at = 0;
    for (count, s) in pairs() {
        let each = s.words();
        let heap: Vec<usize> = (0..each).filter(|&j| s.heap_word(j)).collect();
        for _ in 0..count {
            for &j in &heap {
                masks[(at + j) / 64] |= 1 << ((at + j) % 64);
            }
            at += each;
        }
    }
    let mask = masks.first().copied().unwrap_or(0);
    match words {
        1 => Shape::word(mask == 1).0,
        _ if words <= MASK_WORDS => {
            SHAPE_HEAP | (8 * words as u64) << SHAPE_SIZE_SHIFT | mask << SHAPE_MASK_SHIFT
        }
        _ => large(masks, words),
    }
}

/// The shape of a value of `words` words, more than [`MASK_WORDS`], whose heap words `masks`
/// tells: a pointer to its description, made once.
fn large(masks: Vec<u64>, words: usize) -> u64 {
    let n = words as u64;
    let mut key = masks.clone();
    key.push(n);
    let mut table = LARGE.lock().unwrap_or_else(PoisonError::into_inner);
    let at = *table
        .get_or_insert_with(HashMap::new)
        .entry(key.into_boxed_slice())
        .or_insert_with(|| {
            let large = Box::leak(Box::new(Large {
                words,
                masks: masks.into_boxed_slice(),
            }));
            std::ptr::from_ref(large) as usize
        });
    let at = at as u64;
    assert!(
        at >> (64 - SHAPE_MASK_SHIFT) == 0,
        "a description below 2^48"
    );
    debug_assert!(words > MASK_WORDS);
    (at << SHAPE_MASK_SHIFT) | SHAPE_LARGE
}

/// Copies `n` words from `from` to `to`, which don't overlap: the words of an array held in
/// memory, which compiled code copies whole (generics.large-arrays).
///
/// # Safety
///
/// `from` and `to` each point to `n` words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_copy_words(to: u64, from: u64, n: u64) {
    let to = to as usize as *mut u64;
    let from = from as usize as *const u64;
    let n = usize::try_from(n).expect("under 2^63 words");
    // SAFETY: the caller guarantees the words, which are distinct.
    unsafe { std::ptr::copy_nonoverlapping(from, to, n) }
}

/// Sets `n` words at `to` to 0: an array held in memory that holds nothing.
///
/// # Safety
///
/// `to` points to `n` words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_zero_words(to: u64, n: u64) {
    let to = to as usize as *mut u64;
    let n = usize::try_from(n).expect("under 2^63 words");
    // SAFETY: the caller guarantees the words.
    unsafe { std::ptr::write_bytes(to, 0, n) }
}

/// 1 if word `i` of a value of shape `shape` is a heap word, and otherwise 0.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_shape_heap(shape: u64, i: u64) -> u64 {
    let i = usize::try_from(i).unwrap_or(usize::MAX);
    u64::from(Shape(shape).heap_word(i))
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_rt_large_shape,
        stilt_rt_shape_parts,
        stilt_rt_shape_heap,
        stilt_rt_copy_words,
        stilt_rt_zero_words,
    ]
}

/// The shape of a string, which a list of strings holds.
pub(crate) const STR: Shape = Shape::word(true);

/// The shape of a `u8`, which `str.bytes()` gives a list of.
pub(crate) const U8: Shape = Shape::unsigned(1);

/// The shape of a `u32`, which `str.code_points()` gives a list of.
pub(crate) const U32: Shape = Shape::unsigned(4);

#[cfg(test)]
mod tests {
    use super::{STR, Shape, U8};

    #[test]
    fn shapes_read_back() {
        assert!(STR.heap() && STR.size() == 8 && STR.heap_word(0) && !STR.packed());
        assert!(!U8.heap() && U8.size() == 1 && U8.packed() && !U8.signed() && !U8.counted());
        let i16_shape = Shape(2 | 2 << 2);
        assert!(i16_shape.signed() && i16_shape.size() == 2 && i16_shape.words() == 1);
        let record = Shape(1 | 24 << 2 | 0b101 << 16);
        assert_eq!(record.words(), 3);
        assert!(record.heap_word(0) && !record.heap_word(1) && record.heap_word(2));
        assert!(record.heap() && record.counted() && !Shape::word(false).counted());
        let mut heap = [0u64; 70];
        heap[1] = 1;
        heap[65] = 3;
        // SAFETY: the words are there.
        let large =
            Shape(unsafe { super::stilt_rt_large_shape(heap.as_ptr() as usize as u64, 70) });
        assert_eq!((large.words(), large.size()), (70, 560));
        assert!(large.heap() && large.counted() && !large.packed());
        assert!(large.heap_word(1) && large.heap_word(65) && !large.heap_word(2));
        // SAFETY: as above.
        let again =
            Shape(unsafe { super::stilt_rt_large_shape(heap.as_ptr() as usize as u64, 70) });
        assert_eq!(large, again, "a description is made once");
    }

    #[test]
    fn a_value_of_parts_has_the_words_of_each_in_turn() {
        // Two strings, 20 scalars, then a record of a heap word, a scalar and a heap word.
        let record = Shape(1 | 24 << 2 | 0b101 << 16);
        let parts = [2, STR.0, 20, Shape::word(false).0, 1, record.0];
        // SAFETY: the pairs are there.
        let small =
            Shape(unsafe { super::stilt_rt_shape_parts(parts.as_ptr() as usize as u64, 3) });
        assert_eq!((small.words(), small.size()), (25, 200));
        let heap: Vec<usize> = (0..25).filter(|&i| small.heap_word(i)).collect();
        assert_eq!(heap, [0, 1, 22, 24]);
        assert!(small.heap() && small.counted() && !small.packed());
        // An array of 100 strings, past what a mask holds.
        let strings = [100, STR.0];
        // SAFETY: as above.
        let large =
            Shape(unsafe { super::stilt_rt_shape_parts(strings.as_ptr() as usize as u64, 1) });
        assert_eq!((large.words(), large.size()), (100, 800));
        assert!(large.heap_word(0) && large.heap_word(99) && large.counted());
    }
}
