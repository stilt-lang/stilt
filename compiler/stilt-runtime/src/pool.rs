//! Each thread's memory: small blocks, up to [`LARGEST`] bytes in steps of 8, carved from
//! chunks of [`CHUNK`] bytes and kept once freed, one list for each size, so that a program that
//! allocates small objects at a high rate, as most do, rarely calls the system's allocator (goal
//! debug-speed); and the counts of the objects, bytes and boxes the thread has made less those
//! it has freed.
//!
//! A freed block holds the next block of its list in its first word, so the cache takes no
//! memory of its own beyond the heads of its lists and the free end of the current chunk. A
//! small block is rounded up to its list's size, so any block of a list can serve any request of
//! that size. It never goes back to the system, which didn't give it alone: the cache keeps no
//! more than the program held at its peak. A block freed on another thread than the one that
//! allocated it, as `std.par` frees what its workers made, joins the cache of the thread that
//! frees it.
//!
//! The thread that runs a program's entry owns the one pool that compiled code reaches without a
//! call, [`owner::POOL`], laid out as `crate::layout` says, which the code reads after checking that the
//! thread's pointer is its owner's: an allocation that the pool serves is then a few loads and
//! stores, with no lookup of a thread-local variable, which on macOS is a call. Every other
//! thread, and the owner once its entry has returned, has a pool of its own, which only the
//! runtime reaches. A thread pointer is unique among the threads that run, so no two threads
//! reach one pool at once.
//!
//! A thread adds its counts to the program's totals when it [`flush`]es: a worker of `std.par`
//! after each part of a call it runs, and a program's thread when its entry returns, so that
//! no allocation pays for an atomic instruction that other threads contend for, and the totals
//! are exact once every thread that ran the program's code has flushed (goal no-leaks).
//!
//! The heap holds at most the machine's memory, or the size that `STILT_HEAP` names, read once
//! ([`limit`]), as program.exit-statuses lets an implementation choose.

use std::cell::Cell;
use std::ptr;
use std::sync::atomic::{AtomicI64, AtomicUsize, Ordering};

use crate::layout::{POOL_LARGEST as LARGEST, POOL_LISTS as LISTS};

mod owner;
use owner::owned;
pub(crate) use owner::{own, with};

/// The bytes of a chunk that small blocks are carved from: a program that allocates a structure
/// of millions of nodes, as rbtree does, calls the system's allocator once per chunk instead of
/// once per node, and one that allocates little asks for one chunk, whose pages the system
/// gives as they are first written (goal small-runtime).
const CHUNK: usize = 256 << 10;

/// Whether small blocks come from chunks and are kept once freed: not under the sanitizers, so
/// that they see every block allocated, freed and taken again (goal no-memory-errors). Then no
/// thread owns [`owner::POOL`], and compiled code calls the runtime for every block.
const KEEPS: bool = !cfg!(stilt_sanitizers);
/// The most bytes a program's objects may hold, once [`limit`] has read it, and 0 before.
static LIMIT: AtomicI64 = AtomicI64::new(0);

/// The most bytes a program's objects may hold, as program.exit-statuses lets an implementation
/// choose: the size that `STILT_HEAP` names, a number of bytes that `K`, `M` or `G` may follow
/// for KiB, MiB or GiB, read when the program first allocates, or else the machine's memory. A
/// value that isn't such a size is ignored.
#[cold]
fn limit() -> i64 {
    let known = LIMIT.load(Ordering::Relaxed);
    if known != 0 {
        return known;
    }
    let limit = std::env::var("STILT_HEAP")
        .ok()
        .and_then(|size| parse_size(&size))
        .unwrap_or_else(machine_memory);
    LIMIT.store(limit, Ordering::Relaxed);
    limit
}

/// The bytes that a size such as `512M` names, if it is one.
fn parse_size(size: &str) -> Option<i64> {
    let size = size.trim();
    let (digits, shift) = match size.as_bytes().last()? {
        b'K' | b'k' => (&size[..size.len() - 1], 10),
        b'M' | b'm' => (&size[..size.len() - 1], 20),
        b'G' | b'g' => (&size[..size.len() - 1], 30),
        _ => (size, 0),
    };
    let n: i64 = digits.parse().ok().filter(|&n| n > 0)?;
    n.checked_mul(1 << shift)
}

/// The machine's physical memory, in bytes, or no bound where the system doesn't tell it, as in
/// WebAssembly, whose module's memory bounds what the allocator gives (wasm.limits).
fn machine_memory() -> i64 {
    #[cfg(not(target_family = "wasm"))]
    {
        // SAFETY: `sysconf` has no preconditions.
        let (pages, size) = unsafe {
            (
                libc::sysconf(libc::_SC_PHYS_PAGES),
                libc::sysconf(libc::_SC_PAGESIZE),
            )
        };
        if pages > 0 && size > 0 {
            return pages.saturating_mul(size);
        }
    }
    i64::MAX
}

/// A thread's pool: the thread that owns it, for [`owner::POOL`]; the bytes it may count before it
/// checks the heap's limit again, which it reads once it first allocates ([`limit`]); its counts
/// since it last flushed, which may be below zero on a thread that frees what another made; the
/// free part of its current chunk; and the first block of each list of its cache. Compiled code
/// reads and writes its first fields at the offsets of `crate::layout`.
#[repr(C)]
pub(crate) struct Pool {
    owner: AtomicUsize,
    room: Cell<i64>,
    bytes: Cell<i64>,
    objects: Cell<i64>,
    next: Cell<*mut u8>,
    end: Cell<*mut u8>,
    heads: [Cell<*mut u8>; LISTS],
    boxes: Cell<i64>,
}

impl Pool {
    const fn new() -> Self {
        Pool {
            owner: AtomicUsize::new(0),
            room: Cell::new(0),
            bytes: Cell::new(0),
            objects: Cell::new(0),
            next: Cell::new(ptr::null_mut()),
            end: Cell::new(ptr::null_mut()),
            heads: [const { Cell::new(ptr::null_mut()) }; LISTS],
            boxes: Cell::new(0),
        }
    }
}

/// The counts that threads have flushed.
static OBJECTS: AtomicI64 = AtomicI64::new(0);
static BYTES: AtomicI64 = AtomicI64::new(0);
static BOXES: AtomicI64 = AtomicI64::new(0);

/// The list that keeps blocks of `size` bytes, if the cache keeps them.
fn list(size: usize) -> Option<usize> {
    (KEEPS && size <= LARGEST).then(|| size.div_ceil(8).max(1) - 1)
}

/// The size of a block of `size` bytes: rounded up to its list's size if the cache keeps
/// blocks of that size.
fn rounded(size: usize) -> usize {
    list(size).map_or(size, |l| (l + 1) * 8)
}

impl Pool {
    /// Counts `objects` more objects and `size` more bytes, if the heap still holds them, as
    /// far as this thread and the flushed counts tell, and tells whether it does.
    #[inline]
    fn reserve(&self, objects: i64, size: usize) -> bool {
        let bytes = self.bytes.get() + size as i64;
        if bytes > self.room.get() {
            self.room.set(limit() - BYTES.load(Ordering::Relaxed));
            if bytes > self.room.get() {
                return false;
            }
        }
        self.bytes.set(bytes);
        self.objects.set(self.objects.get() + objects);
        true
    }

    /// A block of `size` bytes, which the cache keeps blocks of: one freed before, or else
    /// one carved from the current chunk, or from a new one, or null when the system has no
    /// memory left.
    #[inline]
    fn take(&self, l: usize) -> *mut u8 {
        let block = self.heads[l].get();
        if !block.is_null() {
            // SAFETY: a block in the cache holds the next block of its list in its first
            // word, and is at least 8 bytes long and aligned.
            self.heads[l].set(unsafe { block.cast::<*mut u8>().read() });
            return block;
        }
        let size = (l + 1) * 8;
        if (self.end.get() as usize) - (self.next.get() as usize) < size {
            // SAFETY: `malloc` has no preconditions.
            let chunk: *mut u8 = unsafe { libc::malloc(CHUNK) }.cast();
            if chunk.is_null() {
                return chunk;
            }
            self.next.set(chunk);
            // SAFETY: the chunk is `CHUNK` bytes long.
            self.end.set(unsafe { chunk.add(CHUNK) });
        }
        let block = self.next.get();
        // SAFETY: the chunk holds at least `size` bytes from `block`.
        self.next.set(unsafe { block.add(size) });
        block
    }

    /// A block of `size` bytes from the list of its size, counted with `objects` objects, if the
    /// list has one and the heap's limit is far.
    #[inline]
    fn cached(&self, size: usize, objects: i64) -> Option<*mut u8> {
        let l = list(size)?;
        let bytes = self.bytes.get() + size as i64;
        let block = self.heads[l].get();
        if block.is_null() || bytes > self.room.get() {
            return None;
        }
        // SAFETY: a block in the cache holds the next block of its list in its first word.
        self.heads[l].set(unsafe { block.cast::<*mut u8>().read() });
        self.bytes.set(bytes);
        self.objects.set(self.objects.get() + objects);
        Some(block)
    }

    /// Gives back a block that [`alloc`] gave for `size` bytes, counted with `objects` objects.
    ///
    /// # Safety
    ///
    /// `block` came from [`alloc`] with this size, and nothing uses it any more.
    #[inline]
    pub(crate) unsafe fn give(&self, block: *mut u8, size: usize, objects: i64) {
        self.bytes.set(self.bytes.get() - size as i64);
        self.objects.set(self.objects.get() - objects);
        match list(size) {
            // SAFETY: as the caller guarantees.
            Some(l) => unsafe { self.keep(block, l) },
            // SAFETY: a block of a size the cache doesn't keep came from the system's allocator.
            None => unsafe { libc::free(block.cast()) },
        }
    }

    /// Keeps a block of list `l` in the cache.
    ///
    /// # Safety
    ///
    /// `block` came from [`Pool::take`] for a block of the list, and nothing uses it.
    #[inline]
    unsafe fn keep(&self, block: *mut u8, l: usize) {
        // SAFETY: the block is at least 8 bytes long and aligned, and nothing uses it.
        unsafe { block.cast::<*mut u8>().write(self.heads[l].get()) };
        self.heads[l].set(block);
    }
}

/// A block of at least `size` bytes, counted with `objects` objects, or null when the system has
/// no memory left or the heap would hold more than its limit.
pub(crate) fn alloc(size: usize, objects: i64) -> *mut u8 {
    crate::limits::allocating();
    if let Some(pool) = owned()
        && let Some(block) = pool.cached(size, objects)
    {
        return block;
    }
    alloc_slowly(size, objects)
}

/// [`alloc`] when the owned pool's lists have no block for it.
#[cold]
#[inline(never)]
fn alloc_slowly(size: usize, objects: i64) -> *mut u8 {
    let block = with(|pool| {
        if !pool.reserve(objects, size) {
            return Some(ptr::null_mut());
        }
        list(size).map(|l| pool.take(l))
    });
    // SAFETY: `malloc` has no preconditions; asking for at least a byte keeps a null result
    // for a system with no memory left.
    block.unwrap_or_else(|| unsafe { libc::malloc(size.max(1)) }.cast())
}

/// Resizes a block that [`alloc`] or this function gave for `old` bytes to `new` bytes, or
/// returns null, leaving it as it was, when the system has no memory left or the heap would
/// hold more than its limit. A block resized to a size the cache keeps moves to a block of that
/// size's list, as a list that grows from empty does, so that it rarely calls the system's
/// allocator.
///
/// # Safety
///
/// `block` came from [`alloc`] or this function with `old` bytes.
pub(crate) unsafe fn realloc(block: *mut u8, old: usize, new: usize) -> *mut u8 {
    crate::limits::allocating();
    let fits = with(|pool| {
        let fits = pool.reserve(0, new);
        if fits {
            pool.bytes.set(pool.bytes.get() - old as i64);
        }
        fits
    });
    if !fits {
        return ptr::null_mut();
    }
    if list(old).is_some() && rounded(old) >= new {
        return block;
    }
    if list(old).is_none() && list(new).is_none() {
        // SAFETY: the caller passes a block from the system's allocator.
        return unsafe { libc::realloc(block.cast(), new) }.cast();
    }
    let moved = match list(new) {
        Some(l) => with(|pool| pool.take(l)),
        // SAFETY: `malloc` has no preconditions.
        None => unsafe { libc::malloc(new) }.cast(),
    };
    if moved.is_null() {
        return moved;
    }
    // SAFETY: both blocks are at least as long as the bytes copied, and distinct; the caller
    // passes a block of `old` bytes that nothing uses after.
    unsafe {
        ptr::copy_nonoverlapping(block, moved, old.min(new));
        give_back(block, old);
    }
    moved
}

/// Keeps a block of `size` bytes in the cache, or gives it back to the system when the cache
/// doesn't keep blocks of its size.
///
/// # Safety
///
/// `block` came from [`alloc`] or [`realloc`] with this size, and nothing uses it any more.
unsafe fn give_back(block: *mut u8, size: usize) {
    match list(size) {
        // SAFETY: as the caller guarantees.
        Some(l) => with(|pool| unsafe { pool.keep(block, l) }),
        // SAFETY: a block of a size the cache doesn't keep came from the system's allocator.
        None => unsafe { libc::free(block.cast()) },
    }
}

/// Gives back a block that [`alloc`] or [`realloc`] gave for `size` bytes, counted with
/// `objects` objects.
///
/// # Safety
///
/// `block` came from one of them with this size, and nothing uses it any more.
pub(crate) unsafe fn free(block: *mut u8, size: usize, objects: i64) {
    if let Some(pool) = owned()
        && let Some(l) = list(size)
    {
        pool.bytes.set(pool.bytes.get() - size as i64);
        pool.objects.set(pool.objects.get() - objects);
        // SAFETY: as the caller guarantees.
        unsafe { pool.keep(block, l) };
        return;
    }
    // SAFETY: as the caller guarantees.
    unsafe { free_slowly(block, size, objects) }
}

/// [`free`] through a thread's own pool, or of a block the cache doesn't keep.
///
/// # Safety
///
/// As [`free`]'s.
#[cold]
#[inline(never)]
unsafe fn free_slowly(block: *mut u8, size: usize, objects: i64) {
    // SAFETY: as the caller guarantees.
    with(|pool| unsafe { pool.give(block, size, objects) });
}

/// A block of `size` bytes for an object, which compiled code asks for when its pool can't
/// serve it inline: the pool is another thread's, its list and chunk are empty, or the heap's
/// limit is near. Null when the heap is full, which the caller reports.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_alloc(size: u64) -> u64 {
    let size = usize::try_from(size).expect("a block under 2^63 bytes");
    crate::object::alloc(size) as u64
}

/// Gives back a block of `size` bytes of an object that compiled code frees itself, when the
/// current thread doesn't own [`owner::POOL`].
///
/// # Safety
///
/// `block` came from [`stilt_rt_alloc`], or the inline path of compiled code, with this size,
/// and nothing uses it any more.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_free(block: u64, size: u64) {
    let size = usize::try_from(size).expect("a block under 2^63 bytes");
    // SAFETY: as the caller guarantees.
    unsafe { crate::object::free(block as *mut u8, size) }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![stilt_rt_alloc, stilt_rt_free]
}

/// The offsets of the fields of a pool that compiled code reads, as `crate::layout` gives them.
#[cfg(test)]
pub(crate) fn offsets() -> [usize; 7] {
    use std::mem::offset_of;
    [
        offset_of!(Pool, owner),
        offset_of!(Pool, room),
        offset_of!(Pool, bytes),
        offset_of!(Pool, objects),
        offset_of!(Pool, next),
        offset_of!(Pool, end),
        offset_of!(Pool, heads),
    ]
}

/// The bytes the heap holds, as far as this thread and the flushed counts tell.
pub(crate) fn held_bytes() -> i64 {
    with(|pool| pool.bytes.get()) + BYTES.load(Ordering::Relaxed)
}

/// Counts a box made (goal inline-values).
pub(crate) fn count_box() {
    with(|pool| pool.boxes.set(pool.boxes.get() + 1));
}

/// Adds the current thread's counts to the totals, and gives up [`owner::POOL`] if the thread owns it,
/// since its entry has returned, so that the next to run a program's entry may own it.
pub(crate) fn flush() {
    with(|pool| {
        for (count, total) in [
            (&pool.objects, &OBJECTS),
            (&pool.bytes, &BYTES),
            (&pool.boxes, &BOXES),
        ] {
            total.fetch_add(count.take(), Ordering::Relaxed);
        }
        pool.room.set(0);
    });
    owner::give_up();
}

/// The objects alive and the boxes made, once the current thread has flushed: exact when every
/// other thread that ran the program's code has flushed too.
pub(crate) fn totals() -> (u64, u64) {
    flush();
    let total = |count: &AtomicI64| count.load(Ordering::Relaxed) as u64;
    (total(&OBJECTS), total(&BOXES))
}

#[cfg(test)]
mod tests;
