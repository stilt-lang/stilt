//! The runtime's own threads, on which the calls of `std.par` run in parts.
//!
//! A call is split into parts, each a run of `f` over some elements, or one closure of
//! `par.both`, which its thread runs from the first to the last. The calling thread runs the
//! first part, and the pool's workers take the others in order, newest call first, so that a
//! call inside a part, whose caller waits for it, ends first. The caller then finishes each
//! part in order: it waits for one that a worker took, and runs one that none has taken itself,
//! so a call never waits for a thread that is busy elsewhere, and calls inside parts can't
//! deadlock however few workers there are. The pool keeps a worker per thread, so that every
//! thread has work while the caller waits; only while the caller runs the first part is there
//! one more thread at work than the number.
//!
//! A part that panics doesn't end the program on its worker. It records how it ended and its
//! worker waits forever, a new one taking its place; its caller, once it has finished every
//! part before it, ends the program the same way on its own thread, through the runtime's usual
//! paths (`crate::panic`, `crate::watch`), so the program reports the panic of the first call in
//! the order of the sequential run, and a watched run or a test ends as it does without threads
//! (par.panics). A part the caller runs itself comes after every part it has finished, so its panic
//! is already the first. Nothing a program prints depends on how many threads there are, or on
//! which runs a part.
//!
//! A watched run that is stopped ends at the next poll of the thread that runs its code, a
//! worker as well (`crate::watch`), and the stop waits for the workers to end their parts.
//!
//! Workers have the stack of the program's own thread (`crate::stacks::STACK`), so a call of `f`
//! may go as deep as anywhere in the program, and running past the end of a worker's stack ends
//! the program with status 134 as on that thread (program.exit-statuses). It ends it at once, from
//! the handler of the fault, which can't wait for the parts before it: a stack overflow, like
//! running out of memory, ends the program wherever it happens, and isn't a panic of .

mod call;
#[cfg(test)]
pub(crate) mod tests;

use std::cell::{Cell, RefCell};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, MutexGuard, OnceLock, PoisonError};
use std::time::{Duration, Instant};

use call::Job;
pub(crate) use call::{Call, Ending};

/// The calls that have parts no thread has taken yet, newest last.
static QUEUE: Mutex<Vec<Arc<Job>>> = Mutex::new(Vec::new());

/// Signalled when a call joins the queue.
static READY: Condvar = Condvar::new();

/// The workers alive: those that wait for a part and those that run one.
static WORKERS: AtomicUsize = AtomicUsize::new(0);

/// The workers that have taken a part and not ended it.
static BUSY: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    /// The part of a call that the current thread runs as a worker.
    static RUNNING: Cell<Option<(*const Job, usize)>> = const { Cell::new(None) };
    /// The calls the current thread has started and not finished, innermost last.
    static OPEN: RefCell<Vec<Arc<Job>>> = const { RefCell::new(Vec::new()) };
}

/// The number of threads a call of `std.par` may run on, the calling thread among them: one per
/// core the system gives the process, or as many as `STILT_THREADS` names, as for the compiler's
/// own threads. No program can tell the number (par.what-runs-in-parallel).
pub(crate) fn threads() -> usize {
    static THREADS: OnceLock<usize> = OnceLock::new();
    #[cfg(test)]
    if let Some(n) = tests::threads() {
        return n;
    }
    *THREADS.get_or_init(|| {
        std::env::var("STILT_THREADS")
            .ok()
            .and_then(|n| n.parse().ok())
            .or_else(|| std::thread::available_parallelism().ok().map(usize::from))
            .unwrap_or(1)
            .max(1)
    })
}

fn queue() -> MutexGuard<'static, Vec<Arc<Job>>> {
    QUEUE.lock().unwrap_or_else(PoisonError::into_inner)
}

/// The workers the pool keeps: one per thread, so that the threads stay busy while a caller
/// waits for a part that a worker took, or none when there is one thread, whose caller runs
/// every part.
fn pool_size() -> usize {
    match threads() {
        1 => 0,
        n => n,
    }
}

/// Puts a call's parts after the first in the queue, and wakes a worker for each, starting the
/// workers that the pool keeps and that aren't alive yet.
fn publish(job: &Arc<Job>, parts: usize) {
    let mut queue = queue();
    while WORKERS.load(Ordering::SeqCst) < pool_size() {
        WORKERS.fetch_add(1, Ordering::SeqCst);
        let started = crate::stacks::spawn("par", work);
        if started.is_err() {
            // The caller runs every part no worker takes.
            WORKERS.fetch_sub(1, Ordering::SeqCst);
            break;
        }
    }
    queue.push(Arc::clone(job));
    for _ in 1..parts.min(pool_size() + 1) {
        READY.notify_one();
    }
    OPEN.with_borrow_mut(|open| open.push(Arc::clone(job)));
}

/// Takes a call that the current thread finished out of the queue.
fn withdraw(job: &Arc<Job>) {
    OPEN.with_borrow_mut(|open| open.retain(|other| !Arc::ptr_eq(other, job)));
    queue().retain(|other| !Arc::ptr_eq(other, job));
}

/// What a worker does: take the next part of the newest call that has one, run it, and say it
/// ended.
fn work() {
    crate::entry::enter();
    loop {
        let (job, k) = take();
        RUNNING.set(Some((Arc::as_ptr(&job), k)));
        job.run(k);
        RUNNING.set(None);
        crate::pool::flush();
        job.done(k);
        BUSY.fetch_sub(1, Ordering::SeqCst);
    }
}

/// The next part of the newest call that has one, waiting until one does, the worker counted
/// busy as it takes it.
fn take() -> (Arc<Job>, usize) {
    let mut queue = queue();
    loop {
        queue.retain(|job| job.open());
        let taken = queue
            .iter()
            .rev()
            .find_map(|job| job.take().map(|k| (Arc::clone(job), k)));
        if let Some(taken) = taken {
            BUSY.fetch_add(1, Ordering::SeqCst);
            return taken;
        }
        queue = READY.wait(queue).unwrap_or_else(PoisonError::into_inner);
    }
}

/// Ends what the current thread runs, which ends the program as `ending` says: the constants it
/// computes are given back (`crate::constants`), no worker takes another part of a call the
/// thread started, and a worker ends its part with `ending`, which
/// the part's caller reports in its turn, and waits forever, with what it held, another taking
/// its place in the pool. Any other thread goes on to end the program itself.
pub(crate) fn end(ending: impl FnOnce() -> Ending) {
    crate::constants::abandon();
    for job in OPEN.with_borrow_mut(std::mem::take) {
        job.close();
    }
    let Some((job, k)) = RUNNING.get() else {
        return;
    };
    // SAFETY: the worker's `work` holds a reference to the job, and never returns.
    unsafe { (*job).end(k, ending()) };
    WORKERS.fetch_sub(1, Ordering::SeqCst);
    BUSY.fetch_sub(1, Ordering::SeqCst);
    loop {
        std::thread::park();
    }
}

/// Whether no worker runs a part of a call, and the current thread has started none that it
/// hasn't finished, so that no other thread runs the code of a call of `std.par` meanwhile.
pub(crate) fn quiet() -> bool {
    BUSY.load(Ordering::SeqCst) == 0 && OPEN.with_borrow(Vec::is_empty)
}

/// Whether no worker runs a part of a call.
pub(crate) fn idle() -> bool {
    BUSY.load(Ordering::SeqCst) == 0
}

/// Waits, until `deadline` at most, for every worker to end the part it runs, as a watched
/// run's workers do at their next poll once it is stopped (`crate::watch`).
pub(crate) fn settle(deadline: Instant) {
    while BUSY.load(Ordering::SeqCst) > 0 && Instant::now() < deadline {
        std::thread::sleep(Duration::from_millis(1));
    }
}
