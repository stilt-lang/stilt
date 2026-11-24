//! Running queries across the machine's cores (Compiler architecture, "Queries"). Each thread
//! has a handle of its own on the database, which shares its memos: a query that another
//! thread is running is waited for rather than run twice. Queries are pure, so what they return
//! doesn't depend on which thread ran them, nor in what order.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, PoisonError};
use std::thread;

use crate::Db;

mod alongside;
mod stacks;

pub use alongside::{Early, map_costly_alongside};
pub use stacks::deep;

/// Below this many items, threads cost more than they save.
const AT_LEAST: usize = 64;

/// How many threads run queries: one per core, or `STILT_THREADS` when it is set.
#[must_use]
pub fn threads() -> usize {
    std::env::var("STILT_THREADS")
        .ok()
        .and_then(|n| n.parse().ok())
        .or_else(|| thread::available_parallelism().ok().map(usize::from))
        .unwrap_or(1)
        .max(1)
}

/// Runs `work` on each of `items` across threads, each with its own handle on `db`, and returns
/// once every item is done.
///
/// # Panics
///
/// Panics when the system can't start a thread, and with the panic of any item's work.
pub fn for_each<D, T>(db: &D, items: &[T], work: impl Fn(&D, &T) + Sync)
where
    D: Db + Clone,
    T: Sync,
{
    let threads = threads().min(items.len() / AT_LEAST);
    if threads <= 1 {
        for item in items {
            work(db, item);
        }
        return;
    }
    let next = AtomicUsize::new(0);
    workers(db, threads, |db| {
        while let Some(item) = items.get(next.fetch_add(1, Ordering::Relaxed)) {
            work(db, item);
        }
    });
}

/// Maps each of `items` by `work` across threads, each with its own handle on `db`, keeping
/// their order: for the work that reads queries and keeps what it finds.
///
/// # Panics
///
/// As [`for_each`].
pub fn map_with<D, T, U>(db: &D, items: &[T], work: impl Fn(&D, &T) -> U + Sync) -> Vec<U>
where
    D: Db + Clone,
    T: Sync,
    U: Send,
{
    let threads = threads().min(items.len() / AT_LEAST);
    if threads <= 1 {
        return items.iter().map(|item| work(db, item)).collect();
    }
    let next = AtomicUsize::new(0);
    let mut done: Vec<(usize, U)> = workers(db, threads, |db| {
        let mut out = Vec::new();
        loop {
            let i = next.fetch_add(1, Ordering::Relaxed);
            let Some(item) = items.get(i) else {
                return out;
            };
            out.push((i, work(db, item)));
        }
    })
    .into_iter()
    .flatten()
    .collect();
    done.sort_unstable_by_key(|&(i, _)| i);
    done.into_iter().map(|(_, u)| u).collect()
}

/// Runs `work` on `threads` threads, each with its own handle on `db`, and returns what each
/// returned once all are done.
fn workers<D, R>(db: &D, threads: usize, work: impl Fn(&D) -> R + Sync) -> Vec<R>
where
    D: Db + Clone,
    R: Send,
{
    thread::scope(|scope| {
        let workers: Vec<_> = (0..threads)
            .map(|_| {
                let db = db.clone();
                let work = &work;
                stacks::spawn(scope, move || work(&db)).expect("a thread for queries")
            })
            .collect();
        // A worker's panic goes on as it began, so that a write to the database, which cancels
        // the queries running on every handle, still reads as a cancellation; a panic of a
        // query goes on first, since the workers it blocked read as cancelled.
        let mut done = Vec::with_capacity(threads);
        let mut panics = Vec::new();
        for worker in workers {
            match worker.join() {
                Ok(r) => done.push(r),
                Err(panic) => panics.push(panic),
            }
        }
        panics.sort_by_key(|panic| panic.is::<salsa::Cancelled>());
        if let Some(panic) = panics.into_iter().next() {
            std::panic::resume_unwind(panic);
        }
        done
    })
}

/// Maps each of `items` by `work` across threads, keeping their order. Each thread takes the
/// next item as it finishes one, so that items of uneven cost spread evenly. The work needs no
/// database, such as what a query's results feed.
///
/// # Panics
///
/// As [`for_each`].
pub fn map<T, U>(items: Vec<T>, work: impl Fn(T) -> U + Sync) -> Vec<U>
where
    T: Send,
    U: Send,
{
    let threads = threads().min(items.len() / AT_LEAST);
    map_on(threads, items, work)
}

/// As [`map`], for work that each item costs more of than starting a thread, as compiling a
/// function does: up to a thread for each item, so that the few functions an edit changes are
/// compiled at once too (goals edit-to-running-program and compile-time-code-rebuilds).
///
/// # Panics
///
/// As [`for_each`].
pub fn map_costly<T, U>(items: Vec<T>, work: impl Fn(T) -> U + Sync) -> Vec<U>
where
    T: Send,
    U: Send,
{
    let threads = threads().min(items.len());
    map_on(threads, items, work)
}

/// Maps each of `items` by `work` on `threads` threads, keeping their order.
fn map_on<T, U>(threads: usize, items: Vec<T>, work: impl Fn(T) -> U + Sync) -> Vec<U>
where
    T: Send,
    U: Send,
{
    if threads <= 1 {
        return items.into_iter().map(work).collect();
    }
    let queue = Mutex::new(items.into_iter().enumerate());
    let mut done: Vec<(usize, U)> = thread::scope(|scope| {
        let workers: Vec<_> = (0..threads)
            .map(|_| {
                let (queue, work) = (&queue, &work);
                stacks::spawn(scope, move || {
                    let mut out = Vec::new();
                    loop {
                        let next = queue.lock().unwrap_or_else(PoisonError::into_inner).next();
                        let Some((i, item)) = next else {
                            return out;
                        };
                        out.push((i, work(item)));
                    }
                })
                .expect("a thread for queries")
            })
            .collect();
        workers
            .into_iter()
            .flat_map(|w| w.join().unwrap_or_else(|e| std::panic::resume_unwind(e)))
            .collect()
    });
    done.sort_unstable_by_key(|&(i, _)| i);
    done.into_iter().map(|(_, u)| u).collect()
}

/// Frees `value` on a thread of its own, so that freeing what a build no longer needs, such as
/// the maps of a module it has written, doesn't hold up the rest of the build (goal
/// compile-time-code-rebuilds). When no thread can start, the calling thread frees it.
pub fn free<T: Send + 'static>(value: T) {
    // A thread that doesn't start drops its closure, and the value with it, here.
    let _ = thread::Builder::new().spawn(move || drop(value));
}
