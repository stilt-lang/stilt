//! Collecting the cycles that values form through `Shared<T>` handles
//! (cycles.through-shared-values). No other value can reach itself (cycles.through-shared-values),
//! and what a handle reaches is marked shared (`super::share`), so only shared objects can be in a
//! cycle, and only they are looked at.
//!
//! A release of a shared object that others still reference makes it a *candidate*: the last
//! reference to a cycle that goes leaves the cycle's counts above zero, and so it is one. The
//! candidates wait in a table, each object holding its place in it, until a collection looks at
//! them by trial deletion ([`trial`]); an object freed meanwhile leaves the table. No shared
//! object is a candidate until a shared value first holds a handle or a task's handle, without
//! which no cycle can form. A collection runs only while no other thread runs the program's
//! code, and never looks into a value that a `when` holds, whose place its block may be writing.

#[cfg(test)]
mod tests;
mod trial;

use std::sync::atomic::{AtomicBool, AtomicI64, AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard, PoisonError};
use std::time::{Duration, Instant};

use super::{DATA, Header, cycle_word};

/// The tag of a `Shared<T>`'s handle, which no variant's index is.
pub(crate) const HANDLE: u16 = u16::MAX - 2;

/// The bits of an object's cycle word: its place among the candidates, counted from 1, or 0
/// when it isn't one; whether a `when` holds it; and its color while a collection runs, black
/// being neither gray nor white.
const PLACE: u32 = (1 << 28) - 1;
const HELD: u32 = 1 << 28;
const GRAY: u32 = 1 << 29;
const WHITE: u32 = 1 << 30;

/// The fewest candidates that start a collection, and the fewest bytes the heap grows by
/// between two collections that its growth starts.
const FEWEST: usize = 1024;
const GROWTH: i64 = 64 * 1024 * 1024;

/// The candidates, by their addresses, 0 for a place that a freed object left.
struct Candidates {
    objects: Vec<usize>,
    count: usize,
}

static CANDIDATES: Mutex<Candidates> = Mutex::new(Candidates {
    objects: Vec::new(),
    count: 0,
});

/// How many candidates there are, which a check reads without the lock.
static COUNT: AtomicUsize = AtomicUsize::new(0);

/// The candidates, and the bytes the heap holds, past which the next collection starts.
static THRESHOLD: AtomicUsize = AtomicUsize::new(FEWEST);
static ROOM: AtomicI64 = AtomicI64::new(GROWTH);

/// Whether a shared value has held a handle or a task's handle, so that releases make
/// candidates.
static WATCHING: AtomicBool = AtomicBool::new(false);

/// Whether a collection runs, so that none starts inside it.
static COLLECTING: AtomicBool = AtomicBool::new(false);

/// Whether threads that a stopped run left running may still reach shared objects, so that no
/// collection may run in this process again.
static FORSAKEN: AtomicBool = AtomicBool::new(false);

fn candidates() -> MutexGuard<'static, Candidates> {
    CANDIDATES.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Whether releases of shared objects make candidates.
pub(super) fn watching() -> bool {
    WATCHING.load(Ordering::SeqCst)
}

/// Notes that a shared value holds `object`, which may close a cycle if it is a handle or a
/// task's handle, so that releases make candidates from then on.
///
/// # Safety
///
/// `object` is alive.
pub(super) unsafe fn meet(object: *mut Header) {
    // SAFETY: the caller guarantees the object is alive.
    let closes = unsafe {
        (*object).kind == DATA && (*object).tag == HANDLE || crate::std_task::is_task(object)
    };
    if closes && !WATCHING.load(Ordering::Relaxed) {
        WATCHING.store(true, Ordering::SeqCst);
    }
}

/// Makes a shared object a candidate, unless it is one, before a release that may leave it
/// referenced.
///
/// # Safety
///
/// `object` is a live shared object, which the caller references.
pub(super) unsafe fn suspect(object: *mut Header) {
    // SAFETY: the caller references the object, so it outlives the call.
    let word = unsafe { cycle_word(object) };
    if word.load(Ordering::Relaxed) & PLACE != 0 {
        return;
    }
    let mut table = candidates();
    if word.load(Ordering::Relaxed) & PLACE != 0 {
        return;
    }
    table.make_room();
    table.objects.push(object as usize);
    // Only a thread that holds the table changes a place, so the bits are 0 until this one.
    word.fetch_or(table.objects.len() as u32, Ordering::Relaxed);
    table.count += 1;
    COUNT.store(table.count, Ordering::Relaxed);
}

/// Forgets an object that is about to be freed, or to be written in place by the one thread that
/// reaches it (`super::claim`), if it is a candidate.
///
/// # Safety
///
/// `object` is alive, and nothing else references it.
pub(super) unsafe fn forget(object: *mut Header) {
    // SAFETY: as the caller guarantees.
    let word = unsafe { cycle_word(object) };
    if word.load(Ordering::Relaxed) & PLACE == 0 {
        return;
    }
    let mut table = candidates();
    let place = (word.load(Ordering::Relaxed) & PLACE) as usize;
    table.objects[place - 1] = 0;
    word.fetch_and(!PLACE, Ordering::Relaxed);
    table.count -= 1;
    COUNT.store(table.count, Ordering::Relaxed);
}

impl Candidates {
    /// Packs the table when freed objects left half of its places, before it grows, so that
    /// it holds at most twice as many places as candidates. Every object it holds is alive,
    /// and its new place replaces the old one in one step, so that no check sees it unplaced.
    fn make_room(&mut self) {
        if self.objects.len() < self.objects.capacity() || 2 * self.count > self.objects.len() {
            return;
        }
        self.objects.retain(|&o| o != 0);
        for (i, &object) in self.objects.iter().enumerate() {
            let place = i as u32 + 1;
            // SAFETY: an object in the table is alive, since it leaves before it is freed.
            let word = unsafe { cycle_word(object as *mut Header) };
            let _ = word.try_update(Ordering::Relaxed, Ordering::Relaxed, |w| {
                Some(w & !PLACE | place)
            });
        }
    }

    /// Takes every candidate out of the table.
    fn take(&mut self) -> Vec<*mut Header> {
        let objects = std::mem::take(&mut self.objects);
        self.count = 0;
        COUNT.store(0, Ordering::Relaxed);
        objects
            .into_iter()
            .filter(|&o| o != 0)
            .map(|o| {
                let object = o as *mut Header;
                // SAFETY: an object in the table is alive.
                unsafe { cycle_word(object) }.fetch_and(!PLACE, Ordering::Relaxed);
                object
            })
            .collect()
    }
}

/// Marks a handle that a `when` holds, whose value the collection doesn't look into.
///
/// # Safety
///
/// `handle` is a live shared value.
pub(crate) unsafe fn hold(handle: u64) {
    // SAFETY: as the caller guarantees.
    unsafe { cycle_word(handle as *mut Header) }.fetch_or(HELD, Ordering::Relaxed);
}

/// Marks a handle that no `when` holds any more.
///
/// # Safety
///
/// `handle` is a live shared value.
pub(crate) unsafe fn unhold(handle: u64) {
    // SAFETY: as the caller guarantees.
    unsafe { cycle_word(handle as *mut Header) }.fetch_and(!HELD, Ordering::Relaxed);
}

/// Whether a `when` holds an object.
///
/// # Safety
///
/// `object` is alive.
unsafe fn held(object: *mut Header) -> bool {
    // SAFETY: as the caller guarantees.
    unsafe { cycle_word(object) }.load(Ordering::Relaxed) & HELD != 0
}

/// Gives up collecting in this process, whose threads a stopped run left running may still
/// reach shared objects (`crate::watch`).
pub(crate) fn forsake() {
    FORSAKEN.store(true, Ordering::SeqCst);
}

/// Whether no task's job runs, and no worker runs a part of a call of `std.par` and the
/// current thread has started none.
fn settled() -> bool {
    crate::tasks::running_jobs() == 0 && crate::workers::quiet()
}

/// Whether no other thread runs the program's code: it has settled, no thread runs code that
/// the sequential run never reaches, and no stopped run left one running.
fn alone() -> bool {
    !FORSAKEN.load(Ordering::SeqCst) && settled() && crate::tasks::unreached_threads() == 0
}

/// Collects, at a point where every count is the program's, once the candidates or the heap
/// have grown past what the last collection left: when `Shared.new` makes a handle and when
/// a `when` lets one go.
pub(crate) fn tick() {
    let count = COUNT.load(Ordering::Relaxed);
    if count == 0 {
        return;
    }
    if count >= THRESHOLD.load(Ordering::Relaxed)
        || crate::pool::held_bytes() >= ROOM.load(Ordering::Relaxed)
    {
        collect();
    }
}

/// Collects, if the program may, so that an allocation that the heap had no room for may be
/// tried again, and tells whether it freed anything.
pub(super) fn collect_for_room() -> bool {
    let before = crate::pool::held_bytes();
    COUNT.load(Ordering::Relaxed) > 0 && collect() && crate::pool::held_bytes() < before
}

/// Collects once the program has ended, before the check that every count is back to zero,
/// after waiting a while for the threads of its tasks and workers to finish their last steps.
pub(crate) fn collect_at_end() {
    if COUNT.load(Ordering::Relaxed) == 0 {
        return;
    }
    let deadline = Instant::now() + Duration::from_secs(10);
    while !settled() && Instant::now() < deadline {
        std::thread::sleep(Duration::from_millis(1));
    }
    collect();
}

/// Runs a collection, if no other thread runs the program's code and none runs already, and
/// tells whether it ran. The next starts once the candidates outnumber twice the candidates
/// that lived on, and once the heap holds twice what it held after, or more by [`GROWTH`].
fn collect() -> bool {
    if !alone() || COLLECTING.swap(true, Ordering::Acquire) {
        return false;
    }
    let roots: Vec<*mut Header> = candidates()
        .take()
        .into_iter()
        // SAFETY: a candidate is alive; one at zero is being freed by the frame that let go
        // of it, which has yet to release what it holds.
        .filter(|&o| unsafe { (*o).rc } != 0)
        .collect();
    // SAFETY: no other thread runs the program's code, so every count is the program's, and
    // only this thread reaches what a collection looks at.
    let lived = unsafe { trial::collect(&roots) };
    THRESHOLD.store(FEWEST.max(2 * lived), Ordering::Relaxed);
    let held = crate::pool::held_bytes();
    ROOM.store(held + held.max(GROWTH), Ordering::Relaxed);
    COLLECTING.store(false, Ordering::Release);
    true
}
