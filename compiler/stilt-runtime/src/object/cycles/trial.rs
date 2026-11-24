//! Trial deletion, the synchronous collection of Bacon and Rajan ("Concurrent Cycle Collection
//! in Reference Counted Systems", ECOOP 2001, section 3): from the candidates, each count drops
//! by the references that the shared objects they reach hold to one another, painting what they
//! reach gray. An object whose count is still above zero is referenced from outside, so it and
//! all it reaches are painted black again and their counts restored; what stays at zero is
//! white, a cycle, or what only cycles reach, which nothing outside references, and is freed.
//!
//! Only shared objects are looked at, since what a shared object holds is shared too
//! (`crate::object::share`), but for the place of a value that a `when` holds, which its block
//! may be writing: a held object counts as referenced from outside, and isn't looked into. Each
//! walk uses a worklist, never the stack.

use super::{GRAY, WHITE, held};
use crate::object::count::{for_each_child, free_object, is_shared};
use crate::object::{Header, cycle_word, drop, pointer};

/// The color bits of an object.
///
/// # Safety
///
/// `object` is alive.
unsafe fn color(object: *mut Header) -> u32 {
    // SAFETY: as the caller guarantees.
    unsafe { cycle_word(object) }.load(std::sync::atomic::Ordering::Relaxed) & (GRAY | WHITE)
}

/// Paints an object `color`: gray, white, or 0 for black.
///
/// # Safety
///
/// `object` is alive, and only this thread reaches it.
unsafe fn paint(object: *mut Header, color: u32) {
    use std::sync::atomic::Ordering::Relaxed;
    // SAFETY: as the caller guarantees.
    let word = unsafe { cycle_word(object) };
    word.store(word.load(Relaxed) & !(GRAY | WHITE) | color, Relaxed);
}

/// The object a heap word points to, if the collection looks at it: a shared object, which is
/// never immortal (`crate::object::share`), so that its count is the collection's to lower.
///
/// # Safety
///
/// `word` is a live heap word.
unsafe fn looked_at(word: u64) -> Option<*mut Header> {
    let object = pointer(word)?;
    // SAFETY: as the caller guarantees.
    unsafe { is_shared(object).then_some(object) }
}

/// Calls `f` on each object that `object` holds and the collection looks at, unless a `when`
/// holds `object`.
///
/// # Safety
///
/// `object` is alive.
unsafe fn children(object: *mut Header, mut f: impl FnMut(*mut Header)) {
    // SAFETY: as the caller guarantees, so its children are alive.
    unsafe {
        if held(object) {
            return;
        }
        for_each_child(object, |word| {
            if let Some(child) = looked_at(word) {
                f(child);
            }
        });
    }
}

/// Frees the cycles among what the live shared objects `roots` reach, and tells how many of
/// the roots live on.
///
/// # Safety
///
/// No other thread runs the program's code, so that every count is the program's.
pub(super) unsafe fn collect(roots: &[*mut Header]) -> usize {
    // SAFETY: as the caller guarantees; each phase reaches only live objects, and the last
    // frees only white ones, which nothing outside the cycles references.
    unsafe {
        for &root in roots {
            if color(root) != GRAY {
                mark_gray(root);
            }
        }
        for &root in roots {
            scan(root);
        }
        let lived = roots.iter().filter(|&&r| color(r) != WHITE).count();
        let mut white = Vec::new();
        for &root in roots {
            gather_white(root, &mut white);
        }
        free_white(&white);
        lived
    }
}

/// Paints gray what `root` reaches, taking from each count the references that what it
/// reaches holds.
///
/// # Safety
///
/// As for [`collect`]; `root` is alive and not gray.
unsafe fn mark_gray(root: *mut Header) {
    // SAFETY: as the caller guarantees; each object is painted gray once, when it is pushed,
    // and takes its references from its children once, when it is popped.
    unsafe {
        paint(root, GRAY);
        let mut pending = vec![root];
        while let Some(object) = pending.pop() {
            children(object, |child| {
                (*child).rc -= 1;
                if color(child) != GRAY {
                    paint(child, GRAY);
                    pending.push(child);
                }
            });
        }
    }
}

/// Paints white what `root` reaches that only gray objects reference, and black again, with
/// its counts restored, what something else references.
///
/// # Safety
///
/// As for [`collect`]; `root` is alive.
unsafe fn scan(root: *mut Header) {
    // SAFETY: as the caller guarantees.
    unsafe {
        let mut pending = vec![root];
        while let Some(object) = pending.pop() {
            if color(object) != GRAY {
                continue;
            }
            if (*object).rc > 0 || held(object) {
                scan_black(object);
                continue;
            }
            paint(object, WHITE);
            children(object, |child| pending.push(child));
        }
    }
}

/// Paints black what `object` reaches, giving back the references that [`mark_gray`] took.
///
/// # Safety
///
/// As for [`collect`]; `object` is alive, and gray or white.
unsafe fn scan_black(object: *mut Header) {
    // SAFETY: as the caller guarantees; each object is painted black once, when it is pushed,
    // and gives its references back to its children once, when it is popped.
    unsafe {
        paint(object, 0);
        let mut pending = vec![object];
        while let Some(object) = pending.pop() {
            children(object, |child| {
                (*child).rc += 1;
                if color(child) != 0 {
                    paint(child, 0);
                    pending.push(child);
                }
            });
        }
    }
}

/// Adds to `white` the white objects that `root` reaches, painting each black so that it is
/// added once.
///
/// # Safety
///
/// As for [`collect`]; `root` is alive.
unsafe fn gather_white(root: *mut Header, white: &mut Vec<*mut Header>) {
    // SAFETY: as the caller guarantees.
    unsafe {
        let mut pending = vec![root];
        while let Some(object) = pending.pop() {
            if color(object) != WHITE {
                continue;
            }
            paint(object, 0);
            white.push(object);
            children(object, |child| pending.push(child));
        }
    }
}

/// Frees the white objects. The references they hold to one another, and to the black objects
/// that [`mark_gray`] took them from, are gone already; any other they hold, to an object the
/// collection doesn't look at, is released once they are all freed, so that no release frees
/// an object that a white one still names.
///
/// # Safety
///
/// As for [`collect`]; nothing outside them references the white objects.
unsafe fn free_white(white: &[*mut Header]) {
    let mut released = Vec::new();
    // SAFETY: as the caller guarantees: every white object is alive until the second loop.
    unsafe {
        for &object in white {
            // A task's handle that goes tells its task, which then keeps its value no longer.
            if crate::std_task::is_task(object) {
                crate::std_task::orphan(object);
            }
            for_each_child(object, |word| {
                if let Some(child) = pointer(word)
                    && looked_at(word).is_none()
                    && (*child).rc != 0
                {
                    released.push(word);
                }
            });
        }
        for &object in white {
            free_object(object);
        }
        for word in released {
            drop(word);
        }
    }
}
