//! Shapes: how a type's values are held, which generic code takes as a type parameter's
//! witness, and which a list keeps for its elements (facts.allocation; goal inline-values).
//! `stilt_runtime::layout` gives the same bits, which `stilt-codegen-clif`'s tests check.
//!
//! A shape is one word. Its lowest bit, [`HEAP`], tells whether the one word that holds a value
//! where a type parameter stands is a heap word: the value's own word, or for a value of
//! several words, its box. The rest tells how a list holds the values as its elements: their
//! size in bytes, from [`SIZE_SHIFT`], which is the width of a scalar narrower than a word, 8
//! for a value of one word and 8 per word for a value held inline; for a narrow scalar, whether
//! its reads extend its sign ([`SIGNED`]); and from [`MASK_SHIFT`], one bit per word of an
//! element that is a heap word.
//!
//! The shape of a value of more than [`MASK_WORDS`] words, which the mask has no room for, has
//! the low bits [`LARGE`], and from [`MASK_SHIFT`] on points to a description of its words that
//! the runtime makes when the code runs. Code that names such an element's type reads and writes
//! it in place by its size alone, which it passes as the constant [`sized`] gives.

/// The bit of the word that holds a value where a type parameter stands being a heap word.
pub const HEAP: u64 = 1;

/// The bit of a narrow scalar whose reads extend its sign.
pub const SIGNED: u64 = 2;

/// Where the size of an element, in bytes, starts, and its bits.
pub const SIZE_SHIFT: u32 = 2;
/// The bits of the size of an element, from [`SIZE_SHIFT`] on.
pub const SIZE_BITS: u64 = 0x3fff;

/// Where the mask of an element's heap words starts.
pub const MASK_SHIFT: u32 = 16;

/// The most words of an element whose heap words a shape's mask tells.
pub const MASK_WORDS: usize = 48;

/// The low bits of the shape of a value of more than [`MASK_WORDS`] words, the rest of which
/// points to the runtime's description of its words.
pub const LARGE: u64 = HEAP | SIGNED;

/// The low bits of the constant that code passes to read and write an element of more than
/// [`MASK_WORDS`] words in place, the rest of which is its size in bytes.
pub const SIZED: u64 = SIGNED;

/// The shape of a value of one word, a heap word if `heap` is set.
#[must_use]
pub const fn word(heap: bool) -> u64 {
    let heap = heap as u64;
    (heap * HEAP) | (8 << SIZE_SHIFT) | (heap << MASK_SHIFT)
}

/// The shape of a scalar of `bytes` bytes, fewer than 8, which a list packs.
#[must_use]
pub const fn packed(bytes: u64, signed: bool) -> u64 {
    (signed as u64 * SIGNED) | (bytes << SIZE_SHIFT)
}

/// The shape of a value of these words, of which those of `heap` are heap words, if it has at
/// most [`MASK_WORDS`] words; a larger one's the runtime makes.
#[must_use]
pub fn of_words(heap: &[bool]) -> Option<u64> {
    if let [h] = heap {
        return Some(word(*h));
    }
    if heap.len() > MASK_WORDS {
        return None;
    }
    let mask = heap
        .iter()
        .enumerate()
        .fold(0, |m, (i, &h)| m | u64::from(h) << i);
    Some(HEAP | ((8 * heap.len() as u64) << SIZE_SHIFT) | (mask << MASK_SHIFT))
}

/// The constant that code passes to read and write in place an element of these words, of
/// which those of `heap` are heap words: its shape, or for a value of more than [`MASK_WORDS`]
/// words, its size.
#[must_use]
pub fn sized(heap: &[bool]) -> u64 {
    of_words(heap).unwrap_or(SIZED | (8 * heap.len() as u64) << MASK_SHIFT)
}

/// The size of an element of this shape, or of the constant [`sized`] gives, in bytes.
#[must_use]
pub const fn size(shape: u64) -> u64 {
    let size = shape >> SIZE_SHIFT & SIZE_BITS;
    if size == 0 && shape & LARGE == SIZED {
        shape >> MASK_SHIFT
    } else {
        size
    }
}

/// Whether a narrow scalar of this shape extends its sign.
#[must_use]
pub const fn signed(shape: u64) -> bool {
    shape & SIGNED != 0
}

#[cfg(test)]
mod tests {
    #[test]
    fn shapes_read_back() {
        assert_eq!(super::size(super::word(true)), 8);
        assert_eq!(super::size(super::packed(1, false)), 1);
        assert!(super::signed(super::packed(4, true)));
        assert_eq!(super::of_words(&[true]), Some(super::word(true)));
        let record = super::sized(&[false, true, false]);
        assert_eq!(super::size(record), 24);
        assert_eq!(record & super::HEAP, 1);
        assert_eq!(record >> super::MASK_SHIFT, 0b010);
        assert_eq!(super::of_words(&[false; 49]), None);
        assert_eq!(super::size(super::sized(&[true; 49])), 8 * 49);
        assert!(super::size(super::sized(&[false; 49])) >= 8);
    }
}
