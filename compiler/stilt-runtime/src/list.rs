//! Lists: growable arrays of elements, copied on write (std.lists).
//!
//! A list object holds, after its header, its length, its capacity, a pointer to its elements
//! and their [`Shape`]. Each element takes the shape's size: the words of a value held inline,
//! one after the other, or a scalar narrower than a word in its own width. The shape tells
//! which words of an element are heap words, so that the list can count and release them
//! without knowing their type.
//!
//! Natives take and give an element in the one word that holds it where a type parameter
//! stands: its own word, a scalar widened to a word, or for a value of several words, its box
//! (`crate::abi`), which [`values`] converts.

use crate::object::{
    HEADER, Header, LIST, alloc_bytes, alloc_object, dup, free_bytes, realloc_bytes, unique,
};
use crate::shape::Shape;

#[cfg(test)]
mod tests;
mod values;

pub(crate) use values::{
    Loan, box_of, get, give_copy, insert, lend, push_value, release, remove, take, update, write,
};

#[repr(C)]
struct Body {
    len: u64,
    cap: u64,
    data: *mut u8,
    shape: u64,
}

/// The size of a list object, its elements apart.
const SIZE: usize = HEADER + std::mem::size_of::<Body>();

/// The offsets in a list's body of its length, its capacity and its pointer to its elements,
/// which `crate::layout` states for compiled code.
#[cfg(test)]
pub(crate) const fn body_offsets() -> (usize, usize, usize) {
    (
        std::mem::offset_of!(Body, len),
        std::mem::offset_of!(Body, cap),
        std::mem::offset_of!(Body, data),
    )
}

/// The body of a list.
///
/// # Safety
///
/// `list` is a live list.
unsafe fn body<'a>(list: *mut Header) -> &'a mut Body {
    // SAFETY: the caller guarantees `list` is a list, whose body follows its header.
    unsafe { &mut *list.cast::<u8>().add(HEADER).cast::<Body>() }
}

fn to_usize(n: u64) -> usize {
    usize::try_from(n).expect("a list of under 2^63 elements")
}

/// A new list of `u8`, one element per byte.
pub(crate) fn of_bytes(bytes: &[u8]) -> *mut Header {
    let xs = new(bytes.len(), crate::shape::U8);
    // SAFETY: the list is new, with room for every byte, which is a `u8` element.
    unsafe {
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), at(xs, 0), bytes.len());
        set_len(xs, bytes.len());
    }
    xs
}

/// The bytes of a list of `u8`, which holds one byte per element.
///
/// # Safety
///
/// `xs` is a live list of `u8`, which outlives the bytes.
pub(crate) unsafe fn as_bytes<'a>(xs: *mut Header) -> &'a [u8] {
    // SAFETY: the caller guarantees the list; its elements are its first `len` bytes.
    unsafe {
        let n = len(xs);
        if n == 0 {
            &[]
        } else {
            std::slice::from_raw_parts(at(xs, 0), n)
        }
    }
}

/// A new empty list with room for `cap` elements of this shape.
pub(crate) fn new(cap: usize, shape: Shape) -> *mut Header {
    let list = alloc_object(SIZE, LIST, 0, 0, 0);
    // SAFETY: the object was allocated with room for its body.
    unsafe {
        list.cast::<u8>().add(HEADER).cast::<Body>().write(Body {
            len: 0,
            cap: cap as u64,
            data: alloc_bytes(cap * shape.size()),
            shape: shape.0,
        });
    }
    list
}

/// The shape of a list's elements.
///
/// # Safety
///
/// `list` is a live list.
pub(crate) unsafe fn shape(list: *mut Header) -> Shape {
    // SAFETY: the caller guarantees the list is alive.
    Shape(unsafe { body(list) }.shape)
}

/// The number of a list's elements.
///
/// # Safety
///
/// `list` is a live list.
pub(crate) unsafe fn len(list: *mut Header) -> usize {
    // SAFETY: the caller guarantees the list is alive.
    to_usize(unsafe { body(list) }.len)
}

/// Sets the number of a unique list's elements, which its first `len` elements hold.
///
/// # Safety
///
/// `list` is a live list that nothing else references, with room for `len` elements, the
/// first `len` of which are set.
pub(crate) unsafe fn set_len(list: *mut Header, len: usize) {
    // SAFETY: the caller guarantees the list is alive and its elements set.
    unsafe { body(list) }.len = len as u64;
}

/// The address of element `i` of a list, which may be one past its last.
///
/// # Safety
///
/// `list` is a live list with room for at least `i` elements.
pub(crate) unsafe fn at(list: *mut Header, i: usize) -> *mut u8 {
    // SAFETY: the caller guarantees the element is within the list's memory.
    unsafe {
        let body = body(list);
        body.data.add(i * Shape(body.shape).size())
    }
}

/// The elements of a list whose elements are one word each.
///
/// # Safety
///
/// `list` is a live list of elements of one word, which outlives the slice and doesn't change
/// while it is used.
pub(crate) unsafe fn words<'a>(list: *mut Header) -> &'a [u64] {
    // SAFETY: the caller guarantees the list is alive; its first `len` elements are set.
    unsafe {
        let body = body(list);
        debug_assert_eq!(
            Shape(body.shape).size(),
            8,
            "a list of one word per element"
        );
        std::slice::from_raw_parts(body.data.cast(), to_usize(body.len))
    }
}

/// The words of element `i` of a list of elements held inline.
///
/// # Safety
///
/// `list` is a live list with more than `i` elements, which outlives the slice and doesn't
/// change while it is used.
pub(crate) unsafe fn element_words<'a>(list: *mut Header, i: usize) -> &'a [u64] {
    // SAFETY: the caller guarantees the element exists; its words are aligned, as every
    // element's size is a multiple of 8 unless it is packed.
    unsafe { std::slice::from_raw_parts(at(list, i).cast(), shape(list).words()) }
}

/// Makes room for at least one more element of a unique list, doubling its capacity when it
/// is full.
///
/// # Safety
///
/// `list` is a live list that nothing else references.
pub(crate) unsafe fn grow(list: *mut Header) {
    // SAFETY: the caller guarantees the list is alive and its own.
    unsafe {
        let body = body(list);
        if body.len < body.cap {
            return;
        }
        let size = Shape(body.shape).size();
        let cap = (body.cap * 2).max(4);
        body.data = realloc_bytes(body.data, to_usize(body.cap) * size, to_usize(cap) * size);
        body.cap = cap;
    }
}

/// Appends a word that the list now owns to a unique list of elements of one word.
///
/// # Safety
///
/// `list` is a live list of elements of one word that nothing else references.
pub(crate) unsafe fn push_word(list: *mut Header, x: u64) {
    // SAFETY: the caller guarantees the list is alive and its own; it grows before it is
    // written past.
    unsafe {
        grow(list);
        let body = body(list);
        body.data.cast::<u64>().add(to_usize(body.len)).write(x);
        body.len += 1;
    }
}

/// Appends the element at `src`, whose references the list takes, to a unique list.
///
/// # Safety
///
/// `list` is a live list that nothing else references, and `src` points to an element of its
/// shape's size, which owns its references.
pub(crate) unsafe fn push_bytes(list: *mut Header, src: *const u8) {
    // SAFETY: the caller guarantees the list is its own and the element's bytes; the list
    // grows before it is written past.
    unsafe {
        grow(list);
        let len = len(list);
        std::ptr::copy_nonoverlapping(src, at(list, len), shape(list).size());
        set_len(list, len + 1);
    }
}

/// A new list of elements of one word of this shape, which owns the given words.
pub(crate) fn from_words(words: &[u64], shape: Shape) -> *mut Header {
    let list = new(words.len(), shape);
    for &w in words {
        // SAFETY: the list is new, so nothing else references it.
        unsafe { push_word(list, w) }
    }
    list
}

/// A new list that copies elements `start` up to `end` of a list, with new references to
/// their heap words, and room for at least `cap` elements.
///
/// # Safety
///
/// `list` is a live list, and `start <= end <= len`.
pub(crate) unsafe fn copy_range(
    list: *mut Header,
    start: usize,
    end: usize,
    cap: usize,
) -> *mut Header {
    // SAFETY: the caller guarantees the list is alive and the range in bounds; the copy has
    // room for it.
    unsafe {
        let shape = shape(list);
        let copy = new(cap.max(end - start), shape);
        std::ptr::copy_nonoverlapping(at(list, start), at(copy, 0), (end - start) * shape.size());
        body(copy).len = (end - start) as u64;
        for_each_heap(copy, |w| dup(w));
        copy
    }
}

/// Copies element `i` of `from` as element `j` of `to`, which must hold nothing there, with
/// new references to its heap words.
///
/// # Safety
///
/// `from` is a live list with more than `i` elements, and `to` a live list of the same shape
/// that nothing else references, with room for element `j`.
pub(crate) unsafe fn copy_element(from: *mut Header, i: usize, to: *mut Header, j: usize) {
    // SAFETY: the caller guarantees both elements' memory.
    unsafe {
        let shape = shape(from);
        std::ptr::copy_nonoverlapping(at(from, i), at(to, j), shape.size());
        if shape.counted() {
            for (k, &w) in element_words(to, j).iter().enumerate() {
                if shape.heap_word(k) {
                    dup(w);
                }
            }
        }
    }
}

/// A copy of a list, which holds new references to its elements.
///
/// # Safety
///
/// `list` is a live list.
pub(crate) unsafe fn copy(list: *mut Header) -> *mut Header {
    // SAFETY: the caller guarantees the list is alive.
    unsafe {
        let len = len(list);
        copy_range(list, 0, len, len)
    }
}

/// Calls `f` on each heap word of a list's elements.
///
/// # Safety
///
/// `list` is a live list.
pub(crate) unsafe fn for_each_heap(list: *mut Header, mut f: impl FnMut(u64)) {
    // SAFETY: the caller guarantees the list is alive, so its elements are.
    unsafe {
        let shape = shape(list);
        if !shape.counted() {
            return;
        }
        let words = shape.words();
        let all = std::slice::from_raw_parts(body(list).data.cast::<u64>(), len(list) * words);
        if words == 1 {
            return all.iter().copied().for_each(f);
        }
        for element in all.chunks_exact(words) {
            for (k, &w) in element.iter().enumerate() {
                if shape.heap_word(k) {
                    f(w);
                }
            }
        }
    }
}

/// Calls `f` on the place of each heap word of a list's elements.
///
/// # Safety
///
/// `list` is a live list, and `f` leaves a heap word in each place.
pub(crate) unsafe fn for_each_heap_place(list: *mut Header, mut f: impl FnMut(*mut u64)) {
    // SAFETY: the caller guarantees the list is alive, so its elements are.
    unsafe {
        let shape = shape(list);
        if !shape.counted() {
            return;
        }
        let words = shape.words();
        let all = body(list).data.cast::<u64>();
        for i in 0..len(list) * words {
            if shape.heap_word(i % words) {
                f(all.add(i));
            }
        }
    }
}

/// Frees a list's elements, which are already released, and returns the size of the list
/// object itself.
///
/// # Safety
///
/// `list` is a list that nothing references.
pub(crate) unsafe fn free_buffer(list: *mut Header) -> usize {
    // SAFETY: the caller guarantees nothing uses the list.
    unsafe {
        let body = body(list);
        free_bytes(body.data, to_usize(body.cap) * Shape(body.shape).size());
    }
    SIZE
}

/// Makes the list a slot holds unique, with room for one more element, and returns it: a
/// shared list is copied with that room, so that a push copies it once.
///
/// # Safety
///
/// `slot` holds a live list, which it owns.
pub(crate) unsafe fn reserve(slot: *mut u64) -> *mut Header {
    // SAFETY: the caller guarantees the slot holds a list it owns.
    unsafe {
        let list = *slot as *mut Header;
        if !crate::object::is_unique(list) && !crate::object::claim(list) {
            let len = len(list);
            let copy = copy_range(list, 0, len, (len * 2).max(4));
            crate::object::drop(*slot);
            *slot = copy as u64;
        }
        let list = *slot as *mut Header;
        grow(list);
        list
    }
}

/// A pointer to element `i` of the list a slot holds, made unique first so that the element
/// can be written, or `None` when `i` is out of bounds.
///
/// # Safety
///
/// `slot` holds a live list, which it owns.
pub(crate) unsafe fn element_slot(slot: *mut u64, i: i64) -> Option<*mut u8> {
    // SAFETY: the caller guarantees the slot holds a list.
    unsafe {
        let list = unique(slot);
        let i = usize::try_from(i).ok().filter(|&i| i < len(list))?;
        Some(at(list, i))
    }
}
