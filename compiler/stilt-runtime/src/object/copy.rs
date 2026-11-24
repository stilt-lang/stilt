//! Deep copies, which a task's function gets at `spawn` under `task.threads()`
//! (tasks.values-in-tasks): every object its captures reach is copied, so that the task
//! and the code that started it share no count, but for those that threads already share, a
//! `Shared<T>`'s handle among them, which keeps its identity (shared.tasks-and-modes), and immortal
//! ones, whose count never changes. A task's handle is shared then (`crate::std_task`), so that
//! both may wait for it. The copy keeps the sharing between the original's objects, and walks them
//! with a worklist, never the stack.

use std::collections::HashMap;

use super::count::is_shared;
use super::{DATA, Header, LIST, MAP, STR, copy_data, for_each_heap_field};
use super::{drop, dup, pointer};
use crate::{list, map, text};

/// A deep copy, and whether it reached an object that threads share or a task's handle, so that
/// its code may reach a `Shared<T>`.
#[derive(Debug)]
pub(crate) struct Copied {
    pub(crate) word: u64,
    pub(crate) handles: bool,
}

/// A deep copy of the value of the heap word `word`, which the caller lends; the copy owns its
/// references.
///
/// # Safety
///
/// `word` is a live heap word, which only the current thread reaches but for what threads
/// share.
pub(crate) unsafe fn deep_copy(word: u64) -> Copied {
    let mut root = word;
    let mut copies: HashMap<usize, u64> = HashMap::new();
    let mut handles = false;
    let mut pending: Vec<*mut u64> = vec![&raw mut root];
    // SAFETY: as the caller guarantees; each place holds a word with a reference of its own,
    // the root's taken here and every other's by the copy that holds it, which the original's
    // other references keep alive.
    unsafe {
        dup(word);
        while let Some(place) = pending.pop() {
            let original = *place;
            let Some(object) = pointer(original) else {
                continue;
            };
            if (*object).rc == 0 || is_shared(object) {
                handles |= (*object).rc != 0;
                continue;
            }
            if crate::std_task::is_task(object) {
                handles = true;
                crate::std_task::cross(object);
                continue;
            }
            let copy = if let Some(&copy) = copies.get(&(object as usize)) {
                dup(copy);
                copy
            } else {
                let copy = shallow(object);
                copies.insert(object as usize, copy);
                places(copy as *mut Header, &mut pending);
                copy
            };
            drop(original);
            *place = copy;
        }
    }
    Copied {
        word: root,
        handles,
    }
}

/// A copy of an object, which holds new references to what it holds.
///
/// # Safety
///
/// `object` is a live object.
unsafe fn shallow(object: *mut Header) -> u64 {
    // SAFETY: as the caller guarantees.
    unsafe {
        match (*object).kind {
            DATA => copy_data(object) as u64,
            STR => text::new(text::bytes(&(object as u64))),
            LIST => list::copy(object) as u64,
            MAP => map::copy(object) as u64,
            kind => unreachable!("a copy of an object of unknown kind {kind}"),
        }
    }
}

/// Adds the place of each heap word that `object` holds to `pending`.
///
/// # Safety
///
/// `object` is a live object, which only the current thread reaches.
unsafe fn places(object: *mut Header, pending: &mut Vec<*mut u64>) {
    // SAFETY: as the caller guarantees.
    unsafe {
        match (*object).kind {
            DATA => for_each_heap_field(object, |p| pending.push(p)),
            LIST => list::for_each_heap_place(object, |p| pending.push(p)),
            MAP => map::for_each_heap_place(object, |p| pending.push(p)),
            _ => {}
        }
    }
}
