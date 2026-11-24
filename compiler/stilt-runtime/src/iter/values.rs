//! The elements that iterators pass along, each in the one word that holds it where a type
//! parameter stands, owning its references: its word, or for a value of several words, a box
//! of them, which the closures of adapters and consumers borrow (`crate::abi`).

use crate::layout::{MASK_WORDS, SHAPE_HEAP, SHAPE_MASK_SHIFT, SHAPE_SIZE_SHIFT};
use crate::list::box_of;
use crate::map::{dup_words, words_of};
use crate::object::{Header, dup, free_box};
use crate::shape::{Shape, stilt_rt_large_shape};

/// Whether a value of this shape takes several words, and so a box.
pub(super) fn boxed(shape: Shape) -> bool {
    shape.size() > 8
}

/// Releases an element that the caller owns.
///
/// # Safety
///
/// `x` is a live value of the shape, which owns its references.
pub(super) unsafe fn release(x: u64, shape: Shape) {
    if shape.heap() {
        // SAFETY: the caller guarantees the value owns its reference.
        unsafe { crate::object::drop(x) };
    }
}

/// A value of its own, with references of its own, of a value the caller lends: a box on the
/// caller's stack becomes a new box.
///
/// # Safety
///
/// `x` is a live value of the shape.
pub(super) unsafe fn owned(x: u64, shape: Shape) -> u64 {
    // SAFETY: the caller guarantees the value; its heap words get new references.
    unsafe {
        if !boxed(shape) {
            if shape.heap() {
                dup(x);
            }
            return x;
        }
        let words = words_of(&x, shape);
        dup_words(words, shape);
        box_of(words, shape)
    }
}

/// The words of an element that the caller owns, which move to the caller's `out`: a box is
/// freed, its words moved out of it, or copied with new references when something else holds
/// it.
///
/// # Safety
///
/// `x` is a live box of the shape, which owns its references, and `out` points to room for its
/// words.
unsafe fn unbox_into(x: u64, shape: Shape, out: *mut u64) {
    // SAFETY: the caller guarantees the box and the room.
    unsafe {
        let words = words_of(&x, shape);
        std::ptr::copy_nonoverlapping(words.as_ptr(), out, words.len());
        let object = x as *mut Header;
        if crate::object::is_unique(object) {
            free_box(object);
        } else {
            dup_words(words, shape);
            crate::object::drop(x);
        }
    }
}

/// The word a native gives back for an element of the shape, whose words go to `out` when it
/// has several (`crate::abi`), or, if `always`, even when it has one.
///
/// # Safety
///
/// `x` owns its references, and `out` points to room for its words.
pub(super) unsafe fn give(x: u64, shape: Shape, out: *mut u64, always: bool) -> u64 {
    // SAFETY: as the caller guarantees.
    unsafe {
        if boxed(shape) {
            unbox_into(x, shape, out);
            0
        } else if always {
            out.write(x);
            0
        } else {
            x
        }
    }
}

/// The words of each part, in order: a part's word, or the words of its box, which are moved
/// out of it.
///
/// # Safety
///
/// Each part is a live value of its shape, which owns its references.
unsafe fn words_of_parts(parts: &[(u64, Shape)]) -> Vec<u64> {
    let mut words = Vec::new();
    for &(x, shape) in parts {
        if boxed(shape) {
            let n = shape.words();
            let mut moved = vec![0; n];
            // SAFETY: the caller guarantees the box, whose words move out.
            unsafe { unbox_into(x, shape, moved.as_mut_ptr()) };
            words.extend(moved);
        } else {
            words.push(x);
        }
    }
    words
}

/// A tuple of the parts, a box of their words, of the shape that [`tuple_shape`] gives them.
///
/// # Safety
///
/// As for [`words_of_parts`].
pub(super) unsafe fn tuple(parts: &[(u64, Shape)], shape: Shape) -> u64 {
    // SAFETY: as the caller guarantees.
    box_of(&unsafe { words_of_parts(parts) }, shape)
}

/// Whether each word of a tuple of values of these shapes is a heap word: a tuple holds each
/// part in the words of its layout, a narrow scalar in a whole word.
fn tuple_heap(parts: &[Shape]) -> Vec<bool> {
    let mut heap = Vec::new();
    for &shape in parts {
        if boxed(shape) {
            heap.extend((0..shape.words()).map(|k| shape.heap_word(k)));
        } else {
            heap.push(shape.heap());
        }
    }
    heap
}

/// The shape of a tuple of values of these shapes, as the compiler gives it (`stilt_mir`'s
/// `shape::of_words`), or the runtime's description of a large one.
pub(super) fn tuple_shape(parts: &[Shape]) -> Shape {
    let heap = tuple_heap(parts);
    if heap.len() > MASK_WORDS {
        let words: Vec<u64> = heap.iter().map(|&h| u64::from(h)).collect();
        // SAFETY: `words` holds one word per word of the tuple.
        return Shape(unsafe {
            stilt_rt_large_shape(words.as_ptr() as usize as u64, words.len() as u64)
        });
    }
    let mask = heap
        .iter()
        .enumerate()
        .fold(0, |m, (i, &h)| m | u64::from(h) << i);
    let size = 8 * heap.len() as u64;
    Shape(SHAPE_HEAP | size << SHAPE_SIZE_SHIFT | mask << SHAPE_MASK_SHIFT)
}
