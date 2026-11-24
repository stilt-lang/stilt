//! Counting references: one more, one less, and freeing an object after its last, with the
//! objects it holds, through a worklist rather than recursion, so that dropping a long chain of
//! nodes can't overflow the stack. Most objects free no child with them, and those never touch
//! the worklist.
//!
//! The count of an object marked [`SHARED`] changes by atomic instructions alone, and that of
//! any other object by plain loads and stores, since only one thread reaches it (Values and
//! costs, "Counts that are atomic only when shared"). The thread that releases a shared
//! object's last reference frees it, once it has seen every earlier release of the others. A
//! release of a shared object that others still reference makes it a candidate for the
//! collection of cycles first (`super::cycles`), which forgets it when it is freed.

use std::cell::RefCell;
use std::sync::atomic::{AtomicU32, Ordering, fence};

use super::data_field;
use super::{DATA, Header, LIST, MAP, SHARED, STR, data_len, data_size, for_each_heap_field};
use super::{cycles, free, pointer};
use crate::layout::{LAYOUT_LARGE, RUNTIME_TAGS};
use crate::map;
use crate::pool::Pool;

thread_local! {
    /// The objects whose count has dropped to zero and which are still to be freed.
    static PENDING: RefCell<Vec<*mut Header>> = const { RefCell::new(Vec::new()) };
}

/// Whether threads share an object, so that its count changes by atomic instructions.
///
/// # Safety
///
/// `object` is alive.
pub(crate) unsafe fn is_shared(object: *mut Header) -> bool {
    // SAFETY: the caller guarantees the object is alive; its flags change only while one thread
    // alone reaches it.
    unsafe { (*object).flags & SHARED != 0 }
}

/// The count of an object that threads share.
///
/// # Safety
///
/// `object` is alive and marked [`SHARED`].
unsafe fn atomic_count<'a>(object: *mut Header) -> &'a AtomicU32 {
    // SAFETY: the caller guarantees the object, whose count is a `u32` that only atomic
    // instructions change.
    unsafe { AtomicU32::from_ptr(&raw mut (*object).rc) }
}

/// The count of an object that threads share, once every earlier release of a reference to it
/// by another thread has been seen.
///
/// # Safety
///
/// `object` is alive and marked [`SHARED`].
pub(super) unsafe fn shared_count(object: *mut Header) -> u32 {
    // SAFETY: as the caller guarantees.
    unsafe { atomic_count(object).load(Ordering::Acquire) }
}

/// Whether a write may change an object in place: nothing else references it, and threads
/// don't share it. A marked object is written in place only once the writer has taken it
/// (`super::claim`), so that whatever a marked object reaches stays marked, as marking relies on
/// (`super::share`).
///
/// # Safety
///
/// `object` is alive.
pub(crate) unsafe fn is_unique(object: *mut Header) -> bool {
    // SAFETY: the caller guarantees the object is alive; only its thread changes the count of
    // an object that isn't shared.
    unsafe { !is_shared(object) && (*object).rc == 1 }
}

/// Counts one more reference to a heap word.
///
/// # Safety
///
/// `word` is a heap word whose object, if any, is alive.
pub(crate) unsafe fn dup(word: u64) {
    if let Some(object) = pointer(word) {
        // SAFETY: the caller guarantees the object is alive.
        unsafe {
            if is_shared(object) {
                atomic_count(object).fetch_add(1, Ordering::Relaxed);
                return;
            }
            let rc = (*object).rc;
            if rc != 0 {
                (*object).rc = rc + 1;
            }
        }
    }
}

/// Counts one reference less to a heap word, and frees its object if that was the last.
///
/// # Safety
///
/// `word` is a heap word that owns one reference to its object, if it has one.
pub(crate) unsafe fn drop(word: u64) {
    if let Some(object) = pointer(word) {
        // SAFETY: the caller owns a reference, so the object is alive.
        if unsafe { release_one(object) } {
            // SAFETY: that was the last reference.
            unsafe { free_all(object) }
        }
    }
}

/// Counts one reference less, and tells whether that was the last.
///
/// # Safety
///
/// `object` is alive, and the caller owns one reference to it.
unsafe fn release_one(object: *mut Header) -> bool {
    // SAFETY: the caller guarantees the object is alive.
    unsafe {
        if is_shared(object) {
            let count = atomic_count(object);
            // Once the count is down, another thread may free the object, so it becomes a
            // candidate before (cycles.can-form-cycle): a count of 1 is this reference's alone.
            if cycles::watching() && count.load(Ordering::Acquire) != 1 {
                cycles::suspect(object);
            }
            if count.fetch_sub(1, Ordering::Release) != 1 {
                return false;
            }
            // What the other threads did with the object comes before its freeing.
            fence(Ordering::Acquire);
            return true;
        }
        match (*object).rc {
            0 => false,
            1 => true,
            rc => {
                (*object).rc = rc - 1;
                false
            }
        }
    }
}

/// Frees an object that nothing references, and every object only it referenced, through the
/// current thread's pool, which it reaches once.
///
/// # Safety
///
/// Nothing references `first` any more.
unsafe fn free_all(first: *mut Header) {
    // Empty, without memory, until a child dies, when it takes the thread's worklist.
    let mut pending = Vec::new();
    // SAFETY: nothing references `first`, nor any object that the worklist takes.
    unsafe {
        if is_small_data(first) {
            free_each(first, &mut pending);
        } else {
            // A list, a map or a string, alone, as most are, frees through the pool without
            // the loop's frame.
            release_children(first, &mut pending);
            free_object(first);
            if let Some(next) = pending.pop() {
                free_each(next, &mut pending);
            }
        }
    }
    if pending.capacity() > 0 {
        give_worklist(pending);
    }
}

/// Frees `first`, which nothing references, and each object of the worklist, with what only it
/// referenced, through the current thread's pool, which it reaches once.
///
/// # Safety
///
/// Nothing references `first`, nor any object of `pending`.
unsafe fn free_each(first: *mut Header, pending: &mut Vec<*mut Header>) {
    crate::pool::with(|pool| {
        let mut object = first;
        loop {
            // SAFETY: nothing references `object`, the first or one on the worklist.
            unsafe {
                if is_small_data(object) {
                    free_data(pool, object, pending);
                } else {
                    release_children(object, pending);
                    free_object(object);
                }
            }
            match pending.pop() {
                Some(next) => object = next,
                None => break,
            }
        }
    });
}

/// The thread's worklist, which the first object freed with another takes, apart so that the
/// compiler can't look its thread-local variable up before it knows it needs it.
#[cold]
#[inline(never)]
fn worklist() -> Vec<*mut Header> {
    PENDING.with_borrow_mut(std::mem::take)
}

/// Gives the thread its worklist back, empty.
#[inline(never)]
fn give_worklist(pending: Vec<*mut Header>) {
    PENDING.with_borrow_mut(|cell| *cell = pending);
}

/// Whether an object is a data object of the program's, not the runtime's, whose layout word
/// holds its heap bits, as most objects freed are.
///
/// # Safety
///
/// `object` is alive.
#[inline]
unsafe fn is_small_data(object: *mut Header) -> bool {
    // SAFETY: as the caller guarantees.
    unsafe {
        (*object).kind == DATA
            && (*object).tag < RUNTIME_TAGS
            && (*object).extent & LAYOUT_LARGE == 0
    }
}

/// Releases the heap words of a small data object that nothing references, adding to `pending`
/// those whose objects had no other reference, and gives its memory to `pool`.
///
/// # Safety
///
/// Nothing references `object`, a small data object of the program's, and `pool` is the current
/// thread's.
#[inline]
unsafe fn free_data(pool: &Pool, object: *mut Header, pending: &mut Vec<*mut Header>) {
    // SAFETY: as the caller guarantees: the object's layout word tells its heap words, each of
    // which held a reference to its object, if it has one.
    unsafe {
        let layout = (*object).extent;
        let len = layout.ilog2();
        let mut mask = layout ^ 1 << len;
        while mask != 0 {
            let child = *data_field(object, mask.trailing_zeros() as usize);
            mask &= mask - 1;
            let Some(child) = pointer(child) else {
                continue;
            };
            let last = if is_shared(child) {
                release_one(child)
            } else {
                match (*child).rc {
                    0 => false,
                    1 => true,
                    rc => {
                        (*child).rc = rc - 1;
                        false
                    }
                }
            };
            if last {
                if pending.capacity() == 0 {
                    *pending = worklist();
                }
                pending.push(child);
            }
        }
        if is_shared(object) {
            cycles::forget(object);
        }
        pool.give(object.cast(), data_size(len as usize), 1);
    }
}

/// Releases the children of an object that nothing references, and adds those that had no
/// other reference to `pending`, which takes the thread's worklist for the first.
///
/// # Safety
///
/// Nothing references `object`, which is alive.
#[inline]
unsafe fn release_children(object: *mut Header, pending: &mut Vec<*mut Header>) {
    let mut release = |child: u64| {
        if let Some(child) = pointer(child)
            // SAFETY: the object held a reference to each of its children, which are alive.
            && unsafe { release_one(child) }
        {
            if pending.capacity() == 0 {
                *pending = worklist();
            }
            pending.push(child);
        }
    };
    // SAFETY: the caller guarantees the object is alive, so its children are.
    unsafe {
        if (*object).kind == DATA {
            // A task's handle that goes tells its task, which then keeps its value no longer.
            if (*object).tag >= RUNTIME_TAGS && crate::std_task::is_task(object) {
                crate::std_task::orphan(object);
            }
            for_each_heap_field(object, |field| release(*field));
        } else {
            for_each_child(object, release);
        }
    }
}

/// Calls `f` on every heap word an object holds.
///
/// # Safety
///
/// `object` is alive.
pub(crate) unsafe fn for_each_child(object: *mut Header, mut f: impl FnMut(u64)) {
    // SAFETY: the caller guarantees the object is alive, so its fields and elements are.
    unsafe {
        match (*object).kind {
            DATA => for_each_heap_field(object, |field| f(*field)),
            LIST => crate::list::for_each_heap(object, f),
            MAP => map::for_each_heap(object, f),
            _ => {}
        }
    }
}

/// Frees an object's own memory, its children already released, and forgets it if it is a
/// candidate for the collection of cycles.
///
/// # Safety
///
/// Nothing references `object`, and its children are released.
pub(super) unsafe fn free_object(object: *mut Header) {
    // SAFETY: the caller guarantees nothing uses the object.
    unsafe {
        // Only a shared object can be a candidate.
        if is_shared(object) {
            cycles::forget(object);
        }
        let size = match (*object).kind {
            DATA => data_size(data_len(object)),
            STR => crate::text::size(object),
            LIST => crate::list::free_buffer(object),
            MAP => map::free_state(object),
            kind => unreachable!("an object of unknown kind {kind}"),
        };
        free(object.cast(), size);
    }
}
