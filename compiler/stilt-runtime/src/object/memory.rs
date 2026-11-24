//! The memory of objects, which the current thread's pool gives and counts (`crate::pool`): a
//! program that would hold more than the heap's limit, or that the system has no memory left for,
//! ends (program.exit-statuses), once a collection of cycles has freed no room for it
//! (cycles.freeing).

use super::{HEADER, Header};
use crate::pool;

/// The number of boxes made since the program started, which is zero when no record, tuple or
/// variant of a type that isn't recursive was ever a heap object (goal inline-values).
pub(crate) fn boxes() -> u64 {
    pool::totals().1
}

/// The number of objects alive, which is zero again when a program has released everything
/// (goal no-leaks), once every thread that ran its code has flushed its counts.
pub(crate) fn live_objects() -> u64 {
    pool::totals().0
}

/// The memory that `ask` gets from the pool, asked again once a collection of cycles has made
/// room, or the end of the program when it gives none.
fn given(ask: impl Fn() -> *mut u8) -> *mut u8 {
    let memory = ask();
    if !memory.is_null() {
        return memory;
    }
    let memory = if super::cycles::collect_for_room() {
        ask()
    } else {
        memory
    };
    if memory.is_null() {
        crate::entry::fatal("out of memory");
    }
    memory
}

/// Allocates `size` bytes for an object, or ends the program when the heap is full.
pub(crate) fn alloc(size: usize) -> *mut u8 {
    given(|| pool::alloc(size.max(HEADER), 1))
}

/// Allocates `size` bytes of memory that an object owns, such as a list's elements, or ends
/// the program when the heap is full.
pub(crate) fn alloc_bytes(size: usize) -> *mut u8 {
    given(|| pool::alloc(size, 0))
}

/// Grows memory that [`alloc_bytes`] gave from `old` bytes to `new`.
///
/// # Safety
///
/// `memory` came from [`alloc_bytes`] or this function, with `old` bytes.
pub(crate) unsafe fn realloc_bytes(memory: *mut u8, old: usize, new: usize) -> *mut u8 {
    // SAFETY: the caller passes memory from `alloc_bytes` or this function, with `old` bytes,
    // which a failed resize leaves as it was.
    given(|| unsafe { pool::realloc(memory, old, new) })
}

/// Allocates an object of `size` bytes with a fresh header, counted once.
pub(crate) fn alloc_object(size: usize, kind: u8, flags: u8, tag: u16, extent: u32) -> *mut Header {
    let object = alloc(size).cast::<Header>();
    // SAFETY: `alloc` returned at least `HEADER` bytes, aligned as `malloc` aligns them.
    unsafe {
        object.write(Header {
            rc: 1,
            kind,
            flags,
            tag,
            extent,
            cycles: 0,
        });
    }
    object
}

/// Gives back an object's memory that [`alloc`] gave, `size` being the size it was asked for.
///
/// # Safety
///
/// `memory` came from [`alloc`] with this size, and nothing uses it any more.
pub(crate) unsafe fn free(memory: *mut u8, size: usize) {
    // SAFETY: the caller passes memory from the pool, with its size, that nothing uses.
    unsafe { pool::free(memory, size.max(HEADER), 1) }
}

/// Gives back memory that [`alloc_bytes`] or [`realloc_bytes`] gave, of `size` bytes.
///
/// # Safety
///
/// `memory` came from one of them with this size, and nothing uses it any more.
pub(crate) unsafe fn free_bytes(memory: *mut u8, size: usize) {
    // SAFETY: the caller passes memory from the pool, with its size, that nothing uses.
    unsafe { pool::free(memory, size, 0) }
}
