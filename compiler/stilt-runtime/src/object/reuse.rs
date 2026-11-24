//! Memory that a data object leaves for another built in its place, as Perceus reuses it
//! (Compiler architecture, "Reference counting"): the release of a value's last reference keeps
//! the memory of its object, once the words it held are released, and the next object of as many
//! fields that the code builds is built there, without the pool. Compiled code does the common
//! case inline (`stilt-codegen-c`'s `stilt.h`) and calls these functions for the rest, as a
//! debug build calls them for all of it.
//!
//! Memory is kept only from an object that no other reference reaches and no other thread can,
//! so nothing can tell it from a fresh one: the program means what it means without reuse
//! (values.consumed-parameters). Kept memory still counts as an object of the heap until it is
//! built in or given back, so the counts that a debug build checks at its end stay exact.

use super::{
    BOX, DATA, Header, alloc_data, data_field, data_field_is_heap, data_len, data_size, drop, free,
    is_unique, mask_words, pointer,
};
use crate::layout::{RUNTIME_TAGS, data_layout};

// The runtime's own tags, a box's and the handles', are those from `RUNTIME_TAGS` on.
const _: () = assert!(RUNTIME_TAGS <= super::HANDLE && RUNTIME_TAGS < BOX);

/// Whether the memory of `object` can be kept for a data object of `len` fields: nothing else
/// references it, no other thread can, and it is a data object of `len` fields that the program
/// built, not one of the runtime's own, such as a task's handle, which its release tells.
///
/// # Safety
///
/// `object` is alive.
unsafe fn keepable(object: *mut Header, len: u64) -> bool {
    // SAFETY: the caller guarantees the object is alive.
    unsafe {
        is_unique(object)
            && (*object).kind == DATA
            && data_len(object) as u64 == len
            && (*object).tag < RUNTIME_TAGS
    }
}

/// Releases a reference to the value `word`, and gives the memory of its object for a data
/// object of `len` fields built in its place when that was the last reference to a data object
/// of `len` fields; and 0 otherwise. The caller takes a reference to each field of the
/// object that a bit of `taken` names, as the words it read of them keep it: the object's own,
/// when its memory is kept, and a new one otherwise. Every other heap word a kept object held is
/// released.
///
/// # Safety
///
/// `word` is a heap word that owns one reference to its object, if it has one, and each field
/// that `taken` names is one of its heap words, of which the caller keeps the word it read.
/// `_known`, what the caller knows of the object (`stilt_mir::mir::known_object`), spares
/// compiled code tests that this makes all the same.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_reclaim(
    word: u64,
    len: u64,
    taken: u64,
    _known: u64,
) -> u64 {
    let Some(object) = pointer(word) else {
        return 0;
    };
    // SAFETY: the caller owns a reference, so the object is alive; a kept object's fields are
    // released or taken, each once, and nothing reads them again.
    unsafe {
        let kept = keepable(object, len);
        for i in 0..data_len(object) {
            let handed = i < 64 && taken >> i & 1 == 1;
            if kept != handed && data_field_is_heap(object, i) {
                let field = *data_field(object, i);
                if kept { drop(field) } else { super::dup(field) }
            }
        }
        if !kept {
            drop(word);
            return 0;
        }
    }
    word
}

/// A data object of `len` fields and tag `tag`, of no heap words until the caller sets its fields
/// and its layout word, in `memory` when [`stilt_rt_reclaim`] kept it, and otherwise new.
///
/// # Safety
///
/// `memory` is 0, or memory that [`stilt_rt_reclaim`] kept for an object of `len` fields and
/// nothing has built in since.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_renew(memory: u64, len: u64, tag: u64) -> u64 {
    let tag = u16::try_from(tag).expect("a variant index under 65536");
    let len = usize::try_from(len).expect("a data object of under 2^63 fields");
    if memory == 0 {
        return alloc_data(len, tag) as u64;
    }
    if tag == BOX {
        crate::pool::count_box();
    }
    let object = memory as *mut Header;
    // SAFETY: the caller guarantees the memory holds a data object of `len` fields that nothing
    // references, whose header and masks this writes again as a new object's.
    unsafe {
        (*object).rc = 1;
        (*object).tag = tag;
        (*object).extent = data_layout(len, 0);
        let masks = data_field(object, len);
        std::ptr::write_bytes(masks, 0, mask_words(len));
    }
    memory
}

/// Gives back memory that [`stilt_rt_reclaim`] kept and nothing was built in.
///
/// # Safety
///
/// `memory` is 0, or memory that [`stilt_rt_reclaim`] kept and nothing has built in since.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_discard(memory: u64) {
    if memory == 0 {
        return;
    }
    let object = memory as *mut Header;
    // SAFETY: the caller guarantees nothing uses the memory, a data object whose fields were
    // released when it was kept.
    unsafe { free(object.cast(), data_size(data_len(object))) }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![stilt_rt_reclaim, stilt_rt_renew, stilt_rt_discard]
}

#[cfg(test)]
mod tests {
    use super::{stilt_rt_discard, stilt_rt_reclaim, stilt_rt_renew};
    use crate::object::{Header, alloc_data, data_field, data_field_is_heap, drop, dup, set_masks};
    use crate::text;

    /// The count of the object a heap word points to.
    fn count(word: u64) -> u32 {
        // SAFETY: each test passes a live object.
        unsafe { (*(word as *mut Header)).rc }
    }

    /// A data object of two fields, `held` and a scalar, with tag 1, which takes a reference to
    /// `held`.
    fn node(held: u64) -> u64 {
        let object = alloc_data(2, 1);
        // SAFETY: the object was just made with two fields, and `held` is a live string.
        unsafe {
            dup(held);
            *data_field(object, 0) = held;
            *data_field(object, 1) = 7;
            set_masks(object, |_| 1);
        }
        object as u64
    }

    #[test]
    fn the_last_reference_keeps_its_memory_for_an_object_of_as_many_fields() {
        let held = text::new(b"held by the node");
        let first = node(held);
        // SAFETY: `first` owns its one reference, which the reclaim takes; the memory it keeps
        // is built in once and given back once.
        unsafe {
            let memory = stilt_rt_reclaim(first, 2, 0, 0);
            assert_eq!(memory, first, "the memory of the last reference is kept");
            assert_eq!(count(held), 1, "the words it held are released");
            let second = stilt_rt_renew(memory, 2, 3);
            assert_eq!(second, first);
            let header = second as *mut Header;
            assert_eq!(((*header).rc, (*header).tag), (1, 3));
            assert!(!data_field_is_heap(header, 0), "it holds no heap word");
            stilt_rt_discard(stilt_rt_reclaim(second, 2, 0, 0));
            drop(held);
        }
    }

    #[test]
    fn a_field_taken_keeps_the_reference_a_kept_object_held() {
        let held = text::new(b"held by the node");
        let first = node(held);
        // SAFETY: the reclaim takes `first`'s one reference and gives its field's to the caller,
        // which releases it, as it releases the memory kept.
        unsafe {
            let memory = stilt_rt_reclaim(first, 2, 1, 0);
            assert_eq!(memory, first);
            assert_eq!(
                count(held),
                2,
                "the field taken keeps the object's reference"
            );
            drop(held);
            stilt_rt_discard(memory);
            drop(held);
        }
    }

    #[test]
    fn a_shared_value_or_another_size_keeps_nothing() {
        let held = text::new(b"held by the node");
        let shared = node(held);
        // SAFETY: `shared` is live; the second reference goes with the first reclaim, the
        // first with the second, which frees it and releases `held`.
        unsafe {
            dup(shared);
            assert_eq!(
                stilt_rt_reclaim(shared, 2, 1, 0),
                0,
                "another reference remains"
            );
            assert_eq!(count(shared), 1);
            assert_eq!(count(held), 3, "the field taken has a reference of its own");
            drop(held);
            assert_eq!(stilt_rt_reclaim(shared, 3, 0, 0), 0, "not of three fields");
            assert_eq!(count(held), 1);
            assert_eq!(
                stilt_rt_reclaim(5, 2, 0, 0),
                0,
                "an immediate holds no object"
            );
            let fresh = stilt_rt_renew(0, 1, 0);
            assert_eq!(count(fresh), 1);
            drop(fresh);
            drop(held);
        }
    }
}
