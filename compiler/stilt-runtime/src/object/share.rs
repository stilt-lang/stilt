//! Marking the objects that threads share (Values and costs, "Counts that are atomic only when
//! shared"; goal atomic-counts-where-shared): before a value reaches another thread, every object
//! it reaches is marked [`SHARED`], so that its count changes by atomic instructions from then on.
//! A mark is removed only from an object that one reference reaches, by the thread that holds it,
//! before it writes the object in place (`super::claim`); any other marked object is copied before
//! a write. So whatever a marked object reaches is marked: a walk stops at a marked object, and a
//! value shared again costs nothing. An immortal object takes no mark, since its count never changes, and the
//! walk goes on to what it holds. The walks use a worklist, never the stack. A walk tells the
//! collection of cycles of each object it finds held inside another, a handle or a task's handle
//! among them, which may close a cycle (`super::cycles`).

use super::count::{for_each_child, is_shared};
use super::{Header, SHARED, cycles, pointer};
use crate::shape::Shape;

/// Marks every object that a value reaches, given in the one word that holds it where a type
/// parameter stands: its word, or for a value of several words, its box.
///
/// # Safety
///
/// `word` is a live value of the shape, and no other thread reaches what it reaches that isn't
/// marked yet.
pub(crate) unsafe fn share(word: u64, shape: Shape) {
    if shape.words() > 1 || shape.heap() {
        // SAFETY: as the caller guarantees.
        unsafe { mark(vec![word], false) }
    }
}

/// Marks every object that a heap word reaches, as [`share`] does, the word being held inside
/// a shared object: a task's value inside its handle.
///
/// # Safety
///
/// As for [`share`].
pub(crate) unsafe fn share_within(word: u64) {
    // SAFETY: as the caller guarantees.
    unsafe { mark(vec![word], true) }
}

/// Marks every object that a marked object holds, which a write in place may have put there:
/// a `when` writes the value of a `Shared<T>` in its place (shared.when).
///
/// # Safety
///
/// `object` is a live object, and no other thread reaches what it holds that isn't marked yet.
pub(crate) unsafe fn share_held(object: *mut Header) {
    let mut pending = Vec::new();
    // SAFETY: as the caller guarantees.
    unsafe {
        for_each_child(object, |child| pending.push(child));
        mark(pending, true);
    }
}

/// Marks what the elements of a list reach through an object that something else references
/// too. An object referenced once, through objects referenced once each, belongs to its
/// element alone, which one thread reads and writes during a call of `std.par`, so it takes no
/// mark, and only what it holds is looked at; the list itself takes none, since the call's
/// threads don't count it. So `par.each` writes such an element in place, and the elements of
/// `[a, a]`, which reach `a` twice, count it atomically.
///
/// # Safety
///
/// `list` is a live list, and no other thread reaches what its elements reach that isn't
/// marked yet.
pub(crate) unsafe fn share_elements(list: *mut Header) {
    let mut pending = Vec::new();
    let mut shared = Vec::new();
    // SAFETY: as the caller guarantees: each object the walk reaches is alive, and only this
    // thread counts an object that isn't marked.
    unsafe {
        crate::list::for_each_heap(list, |word| pending.push(word));
        while let Some(word) = pending.pop() {
            let Some(object) = pointer(word) else {
                continue;
            };
            if is_shared(object) {
                continue;
            }
            if (*object).rc > 1 {
                shared.push(word);
            } else {
                for_each_child(object, |child| pending.push(child));
            }
        }
        mark(shared, false);
    }
}

/// Marks every object that the words of `roots` reach, stopping at marked objects; `within`
/// tells whether a shared object holds the roots.
///
/// # Safety
///
/// The words are live heap words, and no other thread reaches what they reach that isn't
/// marked yet.
unsafe fn mark(roots: Vec<u64>, within: bool) {
    let mut pending: Vec<(u64, bool)> = roots.into_iter().map(|w| (w, within)).collect();
    while let Some((word, inside)) = pending.pop() {
        let Some(object) = pointer(word) else {
            continue;
        };
        // SAFETY: as the caller guarantees; only this thread reaches an object that isn't
        // marked, so it reads its count and writes its flags without atomic instructions.
        unsafe {
            if inside {
                cycles::meet(object);
            }
            if is_shared(object) {
                continue;
            }
            // A task's handle shares the value it ends with, once it ends.
            if crate::std_task::is_task(object) {
                crate::std_task::cross(object);
                continue;
            }
            if (*object).rc != 0 {
                (*object).flags |= SHARED;
            }
            for_each_child(object, |child| pending.push((child, true)));
        }
    }
}
