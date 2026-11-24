//! Data objects of every size of layout word, and their memory kept and taken by another.

use crate::layout::INLINE_FIELDS;
use crate::object::reuse::{stilt_rt_discard, stilt_rt_reclaim, stilt_rt_renew};
use crate::object::{
    Header, alloc_data, data_field, data_field_is_heap, data_len, data_size, drop, dup, set_masks,
    share,
};
use crate::shape::Shape;
use crate::text;

/// The count of the object a heap word points to, which no other thread changes meanwhile.
fn count(word: u64) -> u32 {
    // SAFETY: each test passes a live object.
    unsafe { (*(word as *mut Header)).rc }
}

/// A data object of `len` fields, of which those that `heap` names hold a reference to `s`, and
/// the others their index.
fn node(len: usize, heap: impl Fn(usize) -> bool, s: u64) -> u64 {
    let object = alloc_data(len, 1);
    // SAFETY: the object was just made with `len` fields, and `s` is a live string.
    unsafe {
        for i in 0..len {
            *data_field(object, i) = if heap(i) {
                dup(s);
                s
            } else {
                i as u64
            };
        }
        set_masks(object, |j| {
            (64 * j..len.min(64 * j + 64)).fold(0, |m, i| m | u64::from(heap(i)) << (i % 64))
        });
    }
    object as u64
}

#[test]
fn objects_of_every_size_tell_their_fields_and_release_their_heap_words() {
    let s = text::new(b"a string longer than a word");
    for len in [
        0,
        1,
        2,
        INLINE_FIELDS - 1,
        INLINE_FIELDS,
        INLINE_FIELDS + 1,
        64,
        65,
        200,
    ] {
        let heap = |i: usize| i.is_multiple_of(3) || i + 1 == len;
        let object = node(len, heap, s);
        let held = (0..len).filter(|&i| heap(i)).count();
        assert_eq!(count(s) as usize, 1 + held, "{len} fields");
        // SAFETY: `object` is a live data object of `len` fields, released once.
        unsafe {
            let o = object as *mut Header;
            assert_eq!(data_len(o), len);
            assert!(
                (0..len).all(|i| data_field_is_heap(o, i) == heap(i)),
                "{len}"
            );
            drop(object);
        }
        assert_eq!(count(s), 1, "{len} fields released what they held");
    }
    assert_eq!(data_size(0), 16, "an object of no fields is its header");
    assert_eq!(data_size(INLINE_FIELDS), 16 + 8 * INLINE_FIELDS);
    assert_eq!(
        data_size(INLINE_FIELDS + 1),
        16 + 8 * (INLINE_FIELDS + 2),
        "and a mask word"
    );
    // SAFETY: the test's reference.
    unsafe { drop(s) };
}

#[test]
fn memory_kept_from_a_node_takes_one_whose_fields_change_kind() {
    let (s, t) = (
        text::new(b"held by the first node"),
        text::new(b"held by the second node"),
    );
    let first = node(2, |i| i == 0, s);
    // SAFETY: `first` owns its one reference, which the reclaim takes; the second node is built
    // in its memory, its scalar field where the string was and its string where the scalar was.
    unsafe {
        let memory = stilt_rt_reclaim(first, 2, 0, 0);
        assert_eq!(memory, first);
        assert_eq!(count(s), 1, "the string the first node held is released");
        let second = stilt_rt_renew(memory, 2, 2) as *mut Header;
        dup(t);
        *data_field(second, 0) = 7;
        *data_field(second, 1) = t;
        set_masks(second, |_| 0b10);
        assert!(!data_field_is_heap(second, 0) && data_field_is_heap(second, 1));
        assert_eq!(count(t), 2);
        drop(second as u64);
        assert_eq!((count(s), count(t)), (1, 1), "each string released once");
        // A large node's memory goes back whole when nothing takes it.
        let large = node(INLINE_FIELDS + 5, |i| i == INLINE_FIELDS + 4, s);
        stilt_rt_discard(stilt_rt_reclaim(large, INLINE_FIELDS as u64 + 5, 0, 0));
        assert_eq!(count(s), 1);
        drop(s);
        drop(t);
    }
}

#[test]
fn an_object_that_threads_share_is_freed_by_the_last_to_let_go() {
    let s = text::new(b"reached from two threads");
    let object = node(3, |i| i != 1, s);
    // SAFETY: the object is marked shared before the second thread reaches it, and each thread
    // releases the one reference it holds.
    unsafe {
        drop(s);
        share(object, Shape::word(true));
        dup(object);
        let theirs = std::thread::spawn(move || {
            drop(object);
            crate::pool::flush();
        });
        theirs.join().expect("the thread ends");
        assert_eq!(count(object), 1);
        assert_eq!(count(s), 2, "the fields live while the object does");
        dup(s);
        drop(object);
        assert_eq!(
            count(s),
            1,
            "the last release freed the object and its fields"
        );
        drop(s);
    }
}
