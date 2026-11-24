//! Trial deletion on cycles that each test makes alone, which no other test's thread reaches.

use super::{hold, trial, unhold};
use crate::object::{Header, alloc_data, data_field, drop, dup, set_masks, share};
use crate::shape::Shape;
use crate::text;

/// A data object whose fields are the heap words `fields`, which it takes.
fn node(fields: &[u64]) -> u64 {
    let object = alloc_data(fields.len(), 0);
    // SAFETY: the object was just made with this many fields.
    unsafe {
        for (i, &word) in fields.iter().enumerate() {
            *data_field(object, i) = word;
        }
        set_masks(object, |_| (1 << fields.len()) - 1);
    }
    object as u64
}

/// The count of the object a heap word points to.
fn count(word: u64) -> u32 {
    // SAFETY: each test passes a live object.
    unsafe { (*(word as *mut Header)).rc }
}

/// Two handles in a cycle, the second holding `s` too, marked shared as `Shared.new` and a
/// `when` mark them: the first, which the caller references, and the second.
fn cycle(s: u64) -> (u64, u64) {
    let a = node(&[0]);
    // SAFETY: `a` and `s` are live, and only this thread reaches them.
    unsafe {
        dup(a);
        let b = node(&[a, s]);
        *data_field(a as *mut Header, 0) = b;
        share(a, Shape::word(true));
        (a, b)
    }
}

#[test]
fn a_cycle_that_nothing_else_references_is_freed() {
    let s = text::new(b"held by the cycle");
    // SAFETY: the cycle takes a reference to `s`, and the test keeps its own.
    unsafe { dup(s) };
    let (a, _) = cycle(s);
    // SAFETY: the test lets go of `a`, which the cycle alone references then.
    unsafe {
        drop(a);
        assert_eq!(trial::collect(&[a as *mut Header]), 0);
    }
    assert_eq!(count(s), 1, "the cycle released the string as it was freed");
    // SAFETY: the test's reference.
    unsafe { drop(s) };
}

#[test]
fn a_cycle_that_something_references_lives_on_with_its_counts() {
    let s = text::new(b"kept by the cycle");
    // SAFETY: the cycle takes a reference to `s`, and the test keeps its own.
    unsafe { dup(s) };
    let (a, b) = cycle(s);
    // SAFETY: the test still references `a`, so the cycle lives on.
    unsafe {
        assert_eq!(trial::collect(&[a as *mut Header, b as *mut Header]), 2);
        assert_eq!((count(a), count(b), count(s)), (2, 1, 2));
        drop(a);
        assert_eq!(trial::collect(&[b as *mut Header]), 0);
    }
    assert_eq!(count(s), 1);
    // SAFETY: the test's reference.
    unsafe { drop(s) };
}

#[test]
fn a_held_handle_is_not_looked_into() {
    let s = text::new(b"written by a when");
    // SAFETY: the cycle takes a reference to `s`, and the test keeps its own.
    unsafe { dup(s) };
    let (a, b) = cycle(s);
    // SAFETY: a `when` would hold `b` while its block writes its place, which the collection
    // takes to reference what it holds; once it lets go, the cycle is freed.
    unsafe {
        drop(a);
        hold(b);
        assert_eq!(trial::collect(&[a as *mut Header]), 1);
        assert_eq!((count(a), count(b), count(s)), (1, 1, 2));
        unhold(b);
        assert_eq!(trial::collect(&[a as *mut Header]), 0);
    }
    assert_eq!(count(s), 1);
    // SAFETY: the test's reference.
    unsafe { drop(s) };
}

#[test]
fn a_cycle_through_a_large_object_is_freed() {
    let s = text::new(b"held past the layout word");
    let len = crate::layout::INLINE_FIELDS + 10;
    // SAFETY: the large node holds the handle and `s` in its last two fields, the handle holds
    // the node, and the test lets go of both once they are shared.
    unsafe {
        let handle = node(&[0]);
        dup(handle);
        dup(s);
        let large = alloc_data(len, 0);
        for i in 0..len - 2 {
            *data_field(large, i) = i as u64;
        }
        *data_field(large, len - 2) = handle;
        *data_field(large, len - 1) = s;
        set_masks(large, |j| if j == 0 { 0b11 << (len - 2) } else { 0 });
        *data_field(handle as *mut Header, 0) = large as u64;
        share(handle, Shape::word(true));
        drop(handle);
        assert_eq!(trial::collect(&[handle as *mut Header]), 0);
    }
    assert_eq!(count(s), 1, "the cycle released the string as it was freed");
    // SAFETY: the test's reference.
    unsafe { drop(s) };
}
