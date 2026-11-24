//! Objects: the reference-counted memory behind strings, lists, maps, closures, values of
//! recursive types and the boxes of values of several words.
//!
//! A value is one 64-bit word, or for a record, a tuple or a variant that the compiler holds
//! inline, one word per field. A word is a *scalar*, which is an integer, a float's bits, a
//! `bool` or `()`, or a *heap word*: a pointer to an object, which is 8-byte aligned, or an
//! *immediate*, whose lowest bit is 1, such as a variant without a payload, an inline variant's
//! tag or a string of at most seven bytes held in its word (`crate::text`). Only pointers are
//! counted. Whether a word is a heap word is a fact of its type, which the
//! compiler knows, or which a type parameter's witness, its shape (`crate::shape`), tells generic
//! code.
//!
//! Every object starts with a [`Header`]. A count of 0 marks an immortal object: static data
//! that the compiler emits, such as a string literal or a dictionary, or the box that a list
//! lends an element in, which is never counted or freed. An object is freed when its count drops
//! to zero, and the objects it holds are released with it ([`count`]). An object that threads
//! share is marked [`SHARED`] ([`share`]), and its count changes by atomic instructions alone.
//! Only through a `Shared<T>` can objects reach one another in a cycle, which no count frees,
//! so the shared objects that may be in one are collected by trial deletion ([`cycles`]).

mod copy;
mod count;
mod cycles;
mod memory;
pub(crate) mod reuse;
mod share;
#[cfg(test)]
mod tests;

pub(crate) use copy::deep_copy;
pub(crate) use count::{drop, dup, is_shared, is_unique};
pub(crate) use cycles::{HANDLE, collect_at_end, forsake, hold, tick, unhold};
pub(crate) use memory::{
    alloc, alloc_bytes, alloc_object, boxes, free, free_bytes, live_objects, realloc_bytes,
};
pub(crate) use share::{share, share_elements, share_held, share_within};

pub(crate) use crate::layout::mask_words;
pub(crate) use crate::layout::{BOX, INLINE_FIELDS};
use crate::layout::{LAYOUT_LARGE, data_layout};
use crate::map;

/// The kinds of object.
pub(crate) const DATA: u8 = 0;
pub(crate) const STR: u8 = 1;
pub(crate) const LIST: u8 = 2;
pub(crate) const MAP: u8 = 3;

/// The header of every object.
///
/// A *data object* holds a tuple, a record, a variant's payload, a closure or a dictionary:
/// its fields of one word each, right after the header, so that code can reach a field without
/// knowing how many there are, as a closure's caller reaches its code and generic code a
/// dictionary's methods. Its `tag` is a variant's index among its type's variants, and its
/// `extent` its *layout word*, which tells how many fields it has and which of them are heap
/// words ([`crate::layout::data_layout`]): an object of up to [`INLINE_FIELDS`] fields takes no
/// more than its header and its fields, and a larger one has a *mask* word per 64 fields after
/// them, whose bits tell its heap words.
#[repr(C)]
pub(crate) struct Header {
    /// The reference count, or 0 for an immortal object.
    pub(crate) rc: u32,
    pub(crate) kind: u8,
    /// For any object, [`SHARED`].
    pub(crate) flags: u8,
    pub(crate) tag: u16,
    /// A data object's layout word, a string's room after its bytes, and 0 for other kinds.
    pub(crate) extent: u32,
    /// What the collection of cycles knows of a shared object, which only atomic instructions
    /// change: its place among the candidates, whether a `when` holds it, and its color while
    /// a collection runs ([`cycles`]). Zero for any other object.
    cycles: u32,
}

/// What the collection of cycles knows of an object, its header's last word.
///
/// # Safety
///
/// `object` is alive, and outlives the reference.
pub(crate) unsafe fn cycle_word<'a>(object: *mut Header) -> &'a std::sync::atomic::AtomicU32 {
    // SAFETY: the caller guarantees the object, whose word only atomic instructions change.
    unsafe { std::sync::atomic::AtomicU32::from_ptr(&raw mut (*object).cycles) }
}

/// The size of the header, in bytes.
pub(crate) const HEADER: usize = std::mem::size_of::<Header>();

/// The flag of an object that threads share, whose count only atomic instructions may change
/// (Values and costs, "Counts that are atomic only when shared"). An object takes it before a
/// second thread can reach it, keeps it, and is never written in place again, so whatever a
/// marked object reaches is marked too ([`share`]); a copy of an object never takes it from
/// the original.
pub(crate) const SHARED: u8 = 0x80;

/// The object a word points to, if it is a pointer.
pub(crate) fn pointer(word: u64) -> Option<*mut Header> {
    (word != 0 && word.trailing_zeros() >= 3).then_some(word as *mut Header)
}

/// The size of a data object of `len` fields.
pub(crate) const fn data_size(len: usize) -> usize {
    HEADER + 8 * (mask_words(len) + len)
}

/// The offset of field `i` of a data object.
pub(crate) const fn data_offset(i: usize) -> usize {
    HEADER + 8 * i
}

/// The number of fields of a data object.
///
/// # Safety
///
/// `object` is a live data object.
pub(crate) unsafe fn data_len(object: *mut Header) -> usize {
    // SAFETY: the caller guarantees the object, whose layout word is set.
    let layout = unsafe { (*object).extent };
    if layout & LAYOUT_LARGE == 0 {
        layout.ilog2() as usize
    } else {
        (layout & !LAYOUT_LARGE) as usize
    }
}

/// The address of mask word `j` of a large data object of `len` fields.
///
/// # Safety
///
/// `object` is a live data object of `len` fields, with more than `j` mask words.
unsafe fn mask_word(object: *mut Header, len: usize, j: usize) -> *mut u64 {
    // SAFETY: the caller guarantees the mask word exists.
    unsafe { object.cast::<u8>().add(HEADER + 8 * (len + j)).cast() }
}

/// A pointer to field `i` of a data object.
///
/// # Safety
///
/// `object` is a live data object with more than `i` fields.
pub(crate) unsafe fn data_field(object: *mut Header, i: usize) -> *mut u64 {
    // SAFETY: the caller guarantees the field exists.
    unsafe { object.cast::<u8>().add(data_offset(i)).cast() }
}

/// Whether field `i` of a data object holds a heap word.
///
/// # Safety
///
/// `object` is a live data object with more than `i` fields.
pub(crate) unsafe fn data_field_is_heap(object: *mut Header, i: usize) -> bool {
    // SAFETY: the caller guarantees the object is a data object with this field, so its layout
    // word, and a large one's mask words, are there.
    unsafe {
        let layout = (*object).extent;
        if layout & LAYOUT_LARGE == 0 {
            return layout >> i & 1 == 1;
        }
        *mask_word(object, data_len(object), i / 64) >> (i % 64) & 1 == 1
    }
}

/// Calls `f` with a pointer to each field of a data object that holds a heap word, in order.
///
/// # Safety
///
/// `object` is a live data object.
pub(crate) unsafe fn for_each_heap_field(object: *mut Header, mut f: impl FnMut(*mut u64)) {
    // SAFETY: the caller guarantees the object; each pointer is to one of its fields.
    unsafe {
        let layout = (*object).extent;
        if layout & LAYOUT_LARGE == 0 {
            // The bit above the mask tells the length, and is no field's.
            let mut mask = layout ^ 1 << layout.ilog2();
            while mask != 0 {
                f(data_field(object, mask.trailing_zeros() as usize));
                mask &= mask - 1;
            }
            return;
        }
        let len = data_len(object);
        for j in 0..mask_words(len) {
            let mut mask = *mask_word(object, len, j);
            while mask != 0 {
                f(data_field(object, 64 * j + mask.trailing_zeros() as usize));
                mask &= mask - 1;
            }
        }
    }
}

/// Sets the heap bits of a data object: bit `k` of each `mask(j)` tells whether field
/// `64 * j + k` is a heap word.
///
/// # Safety
///
/// `object` is a live data object.
pub(crate) unsafe fn set_masks(object: *mut Header, mask: impl Fn(usize) -> u64) {
    // SAFETY: the caller guarantees the object, which has `mask_words(len)` mask words.
    unsafe {
        let len = data_len(object);
        if len <= INLINE_FIELDS {
            (*object).extent = data_layout(len, mask(0));
            return;
        }
        for j in 0..mask_words(len) {
            mask_word(object, len, j).write(mask(j));
        }
    }
}

/// Allocates a data object of `len` fields, of no heap words, whose fields are unset.
pub(crate) fn alloc_data(len: usize, tag: u16) -> *mut Header {
    if tag == BOX {
        crate::pool::count_box();
    }
    let object = alloc_object(data_size(len), DATA, 0, tag, data_layout(len, 0));
    let masks = mask_words(len);
    if masks > 0 {
        // SAFETY: the object has `masks` mask words after its fields.
        unsafe { std::ptr::write_bytes(mask_word(object, len, 0), 0, masks) };
    }
    object
}

/// A data object of the given fields in `memory`, `heap` telling which are heap words, whose
/// count of 0 marks it immortal, so that no count frees it: it lives as long as `memory`.
/// The fields are borrowed from their owner, and the object only lends them.
pub(crate) fn lent_data(
    memory: &mut [u64],
    fields: &[u64],
    heap: impl Fn(usize) -> bool,
) -> *mut Header {
    let len = fields.len();
    assert!(memory.len() * 8 >= data_size(len), "room for the fields");
    let object = memory.as_mut_ptr().cast::<Header>();
    // SAFETY: `memory` has room for the header, the fields and their mask words, and is
    // aligned to 8.
    unsafe {
        object.write(Header {
            rc: 0,
            kind: DATA,
            flags: 0,
            tag: BOX,
            extent: data_layout(len, 0),
            cycles: 0,
        });
        std::ptr::copy_nonoverlapping(fields.as_ptr(), data_field(object, 0), len);
        set_masks(object, |j| {
            (64 * j..len.min(64 * j + 64)).fold(0, |m, i| m | u64::from(heap(i)) << (i % 64))
        });
    }
    object
}

/// Frees a box that nothing else references, whose fields have moved out of it.
///
/// # Safety
///
/// `object` is a live data object with a count of 1, whose fields nothing reads again.
pub(crate) unsafe fn free_box(object: *mut Header) {
    // SAFETY: the caller guarantees the object is a data object that only it references.
    unsafe {
        cycles::forget(object);
        free(object.cast(), data_size(data_len(object)));
    }
}

/// Makes the object a slot holds unique, copying it if it is shared, and returns it. This is
/// copy-on-write: a write to a value changes its object in place only when no other value
/// shares it ([`is_unique`], [`claim`]).
///
/// # Safety
///
/// `slot` holds a pointer to a live data object, list or map, which it owns.
pub(crate) unsafe fn unique(slot: *mut u64) -> *mut Header {
    // SAFETY: the caller guarantees the slot holds a live object it owns.
    unsafe {
        let object = *slot as *mut Header;
        if is_unique(object) || claim(object) {
            return object;
        }
        let copy = match (*object).kind {
            DATA => copy_data(object),
            LIST => crate::list::copy(object),
            MAP => map::copy(object),
            kind => unreachable!("a write to an object of kind {kind}"),
        };
        drop(*slot);
        *slot = copy as u64;
        copy
    }
}

/// Takes for a write in place an object that threads may share, which its mark says, but that
/// one reference reaches, the writer's: no other thread can reach it, so it is the writer's
/// alone. It leaves the candidates for the collection of cycles and loses its mark, which what
/// it then holds needn't have; sharing it again marks it and what it holds (`share`), as the end
/// of a `when` does with what its block left in a handle's value. Without this, every `when`
/// that writes the value would copy it first (shared.when).
///
/// # Safety
///
/// `object` is alive, and the caller owns a reference to it.
pub(crate) unsafe fn claim(object: *mut Header) -> bool {
    // SAFETY: as the caller guarantees. A count of 1 is the caller's reference alone, which no
    // other thread can copy, so no other thread reads the flags or the count meanwhile.
    unsafe {
        if !is_shared(object) || count::shared_count(object) != 1 {
            return false;
        }
        cycles::forget(object);
        (*object).flags &= !SHARED;
        true
    }
}

/// A copy of a data object, which holds new references to its heap fields.
///
/// # Safety
///
/// `object` is a live data object.
unsafe fn copy_data(object: *mut Header) -> *mut Header {
    // SAFETY: the caller guarantees the object is alive; the copy has the same size.
    unsafe {
        let size = data_size(data_len(object));
        let copy = alloc(size).cast::<Header>();
        std::ptr::copy_nonoverlapping(object.cast::<u8>(), copy.cast::<u8>(), size);
        (*copy).rc = 1;
        (*copy).flags &= !SHARED;
        (*copy).cycles = 0;
        for_each_heap_field(copy, |field| dup(*field));
        copy
    }
}
