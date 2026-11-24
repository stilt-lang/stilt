//! An element of a list in the one word that holds it where a type parameter stands, in code
//! compiled for arguments of one word: its own word, a scalar narrower than a word widened to
//! one, or for a value of several words, its box; and an element as a native gives it, its words
//! written to memory that its caller passes when it has several (`crate::abi`).

use super::{at, body, element_words, grow, len, set_len, shape};
use crate::layout::MASK_WORDS;
use crate::object::{
    Header, alloc_data, data_field, data_size, dup, free_box, lent_data, set_masks,
};
use crate::shape::Shape;

/// Reads a packed scalar of this shape, widened to a word.
///
/// # Safety
///
/// `p` points to an element of this packed shape.
unsafe fn read_packed(p: *const u8, shape: Shape) -> u64 {
    // SAFETY: the caller guarantees `p` points to `shape.size()` bytes.
    unsafe {
        match (shape.size(), shape.signed()) {
            (1, false) => u64::from(p.read()),
            (1, true) => p.cast::<i8>().read() as u64,
            (2, false) => u64::from(p.cast::<u16>().read_unaligned()),
            (2, true) => p.cast::<i16>().read_unaligned() as u64,
            (_, false) => u64::from(p.cast::<u32>().read_unaligned()),
            (_, true) => p.cast::<i32>().read_unaligned() as u64,
        }
    }
}

/// Writes a scalar as a packed element of this shape.
///
/// # Safety
///
/// `p` points to room for an element of this packed shape.
unsafe fn write_packed(p: *mut u8, shape: Shape, x: u64) {
    // SAFETY: the caller guarantees `p` points to `shape.size()` bytes.
    unsafe {
        match shape.size() {
            1 => p.write(x as u8),
            2 => p.cast::<u16>().write_unaligned(x as u16),
            _ => p.cast::<u32>().write_unaligned(x as u32),
        }
    }
}

/// The box of the words of an element held inline, which owns them: the words become the
/// box's, with no new reference.
pub(crate) fn box_of(words: &[u64], shape: Shape) -> u64 {
    let object = alloc_data(words.len(), crate::object::BOX);
    // SAFETY: the object was just allocated with this many fields.
    unsafe {
        std::ptr::copy_nonoverlapping(words.as_ptr(), data_field(object, 0), words.len());
        set_masks(object, |j| shape.mask(j));
    }
    object as u64
}

/// Element `i` of a list, in the one word that holds it where a type parameter stands, which
/// takes the element's references without counting new ones: the caller has taken the element
/// out of the list, or counts them.
///
/// # Safety
///
/// `list` is a live list with more than `i` elements.
pub(crate) unsafe fn take(list: *mut Header, i: usize) -> u64 {
    // SAFETY: the caller guarantees the element exists.
    unsafe {
        let shape = shape(list);
        let p = at(list, i);
        if shape.packed() {
            read_packed(p, shape)
        } else if shape.size() == 8 {
            p.cast::<u64>().read()
        } else {
            box_of(element_words(list, i), shape)
        }
    }
}

/// Element `i` of a list, in the one word that holds it where a type parameter stands, with
/// references of its own.
///
/// # Safety
///
/// `list` is a live list with more than `i` elements.
pub(crate) unsafe fn get(list: *mut Header, i: usize) -> u64 {
    // SAFETY: the caller guarantees the element exists; its heap words get new references
    // before the word that holds them is given.
    unsafe {
        dup_element(list, i);
        take(list, i)
    }
}

/// Element `i` of a list, with references of its own, as a native gives it ([`give`]).
///
/// # Safety
///
/// As for [`give`].
pub(crate) unsafe fn give_copy(list: *mut Header, i: usize, out: *mut u64) -> u64 {
    // SAFETY: as for `get`.
    unsafe {
        dup_element(list, i);
        give(list, i, out)
    }
}

/// Counts a new reference to each heap word of element `i` of a list.
///
/// # Safety
///
/// `list` is a live list with more than `i` elements.
unsafe fn dup_element(list: *mut Header, i: usize) {
    // SAFETY: the caller guarantees the element exists.
    unsafe {
        let shape = shape(list);
        if shape.counted() {
            for (k, &w) in element_words(list, i).iter().enumerate() {
                if shape.heap_word(k) {
                    dup(w);
                }
            }
        }
    }
}

/// Room for the box that [`lend`] lends: a header, the words of an element, and its masks, on
/// the stack for an element of at most [`MASK_WORDS`] words, and otherwise from the allocator,
/// as a buffer that no count sees.
pub(crate) struct Loan {
    inline: [u64; 3 + MASK_WORDS],
    large: Vec<u64>,
}

impl Loan {
    pub(crate) const fn new() -> Self {
        Self {
            inline: [0; 3 + MASK_WORDS],
            large: Vec::new(),
        }
    }

    /// Room for a box of `len` fields.
    pub(crate) fn room(&mut self, len: usize) -> &mut [u64] {
        let words = data_size(len) / 8;
        if words <= self.inline.len() {
            &mut self.inline
        } else {
            self.large.resize(words, 0);
            &mut self.large
        }
    }
}

/// Element `i` of a list, in the one word that holds it where a type parameter stands, lent
/// without references of its own: for an element of several words, a box in `loan`, which no
/// count frees and which lives as long as `loan`. The structural impls lend elements to the
/// methods of `Eq`, `Ord`, `Hash` and `Show`, whose results can't hold them, so that comparing,
/// hashing and showing a list allocates nothing for its elements.
///
/// # Safety
///
/// `list` is a live list with more than `i` elements, which outlives the word and doesn't
/// change while it is used.
pub(crate) unsafe fn lend(list: *mut Header, i: usize, loan: &mut Loan) -> u64 {
    // SAFETY: the caller guarantees the element exists.
    unsafe {
        let shape = shape(list);
        if shape.size() <= 8 {
            return take(list, i);
        }
        let words = element_words(list, i);
        lent_data(loan.room(words.len()), words, |k| shape.heap_word(k)) as u64
    }
}

/// Writes `x`, which the caller keeps, as element `i` of a list, which must hold nothing
/// there: the element counts new references to its heap words.
///
/// # Safety
///
/// `list` is a live list that nothing else references, with room for element `i`, and `x` a
/// live value of its elements' type, in the one word that holds it where a type parameter
/// stands.
pub(crate) unsafe fn write(list: *mut Header, i: usize, x: u64) {
    // SAFETY: the caller guarantees the room and the value; a box of several words holds
    // as many fields as an element has words.
    unsafe {
        let shape = shape(list);
        let p = at(list, i);
        if shape.packed() {
            return write_packed(p, shape, x);
        }
        let words = shape.words();
        for k in 0..words {
            let w = if words == 1 {
                x
            } else {
                *data_field(x as *mut Header, k)
            };
            if shape.heap_word(k) {
                dup(w);
            }
            p.cast::<u64>().add(k).write(w);
        }
    }
}

/// Appends `x`, which it consumes, to a unique list: a box of several words that nothing else
/// references gives its words to the element, and is freed alone.
///
/// # Safety
///
/// `list` is a live list that nothing else references, and `x` a live value of its elements'
/// type, in the one word that holds it where a type parameter stands, which owns its
/// references.
pub(crate) unsafe fn push_value(list: *mut Header, x: u64) {
    // SAFETY: the caller guarantees the list and the value; the list grows before it is
    // written past, and a unique box's fields move to the element before it is freed.
    unsafe {
        grow(list);
        let len = len(list);
        let shape = shape(list);
        if shape.size() > 8 && crate::object::is_unique(x as *mut Header) {
            let words = std::slice::from_raw_parts(data_field(x as *mut Header, 0), shape.words());
            std::ptr::copy_nonoverlapping(words.as_ptr(), at(list, len).cast(), words.len());
            free_box(x as *mut Header);
        } else {
            write(list, len, x);
            if shape.heap() {
                crate::object::drop(x);
            }
        }
        set_len(list, len + 1);
    }
}

/// Releases the heap words of element `i` of a list, which no longer holds them.
///
/// # Safety
///
/// `list` is a live list with more than `i` elements, which own their references.
pub(crate) unsafe fn release(list: *mut Header, i: usize) {
    // SAFETY: the caller guarantees the element exists and owns its words.
    unsafe {
        let shape = shape(list);
        if shape.packed() {
            return;
        }
        for (k, &w) in element_words(list, i).iter().enumerate() {
            if shape.heap_word(k) {
                crate::object::drop(w);
            }
        }
    }
}

/// Element `i` of a list, as a native gives it (`crate::abi`): in the one word that holds it,
/// or for an element of several words held inline, its words written to the memory `out`
/// points to, and 0, or where `out` is null, as code past the caps of instances passes, its
/// box. It takes the element's references without counting new ones.
///
/// # Safety
///
/// `list` is a live list with more than `i` elements, and `out` points to room for the words of
/// an element of several words.
pub(crate) unsafe fn give(list: *mut Header, i: usize, out: *mut u64) -> u64 {
    // SAFETY: the caller guarantees the element and the room.
    unsafe {
        if shape(list).size() <= 8 || out.is_null() {
            return take(list, i);
        }
        let words = element_words(list, i);
        std::ptr::copy_nonoverlapping(words.as_ptr(), out, words.len());
        0
    }
}

/// Removes element `i` of a unique list, and gives it, now owned by the caller, as [`give`]
/// does.
///
/// # Safety
///
/// `list` is a live list that nothing else references, with more than `i` elements, and `out`
/// points to room for the words of an element of several words.
pub(crate) unsafe fn remove(list: *mut Header, i: usize, out: *mut u64) -> u64 {
    // SAFETY: the caller guarantees the element exists.
    unsafe {
        let x = give(list, i, out);
        let len = len(list);
        // Removing the last element, as `pop` does, moves nothing, and calls nothing.
        if i + 1 < len {
            std::ptr::copy(
                at(list, i + 1),
                at(list, i),
                (len - i - 1) * shape(list).size(),
            );
        }
        body(list).len -= 1;
        x
    }
}

/// Inserts `x`, which the caller keeps, at index `i` of a unique list.
///
/// # Safety
///
/// `list` is a live list that nothing else references, with at least `i` elements, and `x` a
/// live value of its elements' type.
pub(crate) unsafe fn insert(list: *mut Header, i: usize, x: u64) {
    // SAFETY: the caller guarantees the index is in bounds; the list grows first.
    unsafe {
        grow(list);
        let len = len(list);
        if i < len {
            std::ptr::copy(at(list, i), at(list, i + 1), (len - i) * shape(list).size());
        }
        write(list, i, x);
        body(list).len += 1;
    }
}

/// Lends element `i` of a unique list to `f` as the words of its layout, a narrow scalar widened
/// to a word, which `f` may change in place and which then become the element's: the words
/// move out and back, so no count changes but those `f` makes.
///
/// # Safety
///
/// `list` is a live list that nothing else references, with more than `i` elements, which
/// nothing reaches while `f` runs, and `f` leaves live words of the element's type.
pub(crate) unsafe fn update(list: *mut Header, i: usize, f: impl FnOnce(&mut [u64])) {
    // SAFETY: the caller guarantees the element and that only `f` changes it meanwhile.
    unsafe {
        let shape = shape(list);
        let p = at(list, i);
        if shape.packed() {
            let mut word = [read_packed(p, shape)];
            f(&mut word);
            return write_packed(p, shape, word[0]);
        }
        let mut words = element_words(list, i).to_vec();
        f(&mut words);
        std::ptr::copy_nonoverlapping(words.as_ptr(), p.cast::<u64>(), words.len());
    }
}
