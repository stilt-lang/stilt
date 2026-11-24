//! The threads that tasks run on: a pool of threads with the program's stack (`crate::entry`),
//! so that a stack overflow in a task ends the program with status 134 as in `main`, each kept
//! once its job ends for the next, up to [`KEPT`] idle ones. A thread is started for a job when
//! none is idle, so a task that waits for another never waits for a thread; past [`MOST`]
//! running jobs, or when the system starts no more threads, the caller runs the job itself,
//! as the sequential run does.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc::{Receiver, Sender, channel};
use std::sync::{Mutex, PoisonError};

use crate::entry::enter;

/// A job: the code a thread runs.
pub(crate) type Job = Box<dyn FnOnce() + Send>;

/// The most idle threads kept.
const KEPT: usize = 16;

/// The most jobs running at once.
const MOST: usize = 512;

/// The idle threads, each by the channel it takes its next job from.
static IDLE: Mutex<Vec<Sender<Job>>> = Mutex::new(Vec::new());

/// The jobs running.
static RUNNING: AtomicUsize = AtomicUsize::new(0);

/// How many jobs run on the pool's threads, or are about to.
pub(crate) fn running() -> usize {
    RUNNING.load(Ordering::Acquire)
}

/// Whether a job can start on a thread now. A caller that is told so must call [`start`].
pub(crate) fn reserve() -> bool {
    RUNNING.fetch_add(1, Ordering::AcqRel) < MOST || {
        RUNNING.fetch_sub(1, Ordering::AcqRel);
        false
    }
}

/// Runs `job` on a thread of the pool, after [`reserve`] said one can start, or gives it back
/// when the system starts no thread.
pub(crate) fn start(job: Job) -> Result<(), Job> {
    let mut job = job;
    loop {
        let idle = IDLE.lock().unwrap_or_else(PoisonError::into_inner).pop();
        let Some(idle) = idle else { break };
        match idle.send(job) {
            Ok(()) => return Ok(()),
            // A thread that ended after it said it was idle.
            Err(e) => job = e.0,
        }
    }
    let (tx, rx) = channel();
    let first = std::sync::Arc::new(Mutex::new(Some(job)));
    let theirs = std::sync::Arc::clone(&first);
    let started = crate::stacks::spawn("task", move || {
        let job = theirs.lock().unwrap_or_else(PoisonError::into_inner).take();
        work(job, &tx, &rx);
    });
    if started.is_ok() {
        return Ok(());
    }
    RUNNING.fetch_sub(1, Ordering::AcqRel);
    let job = first.lock().unwrap_or_else(PoisonError::into_inner).take();
    Err(job.expect("a job that no thread took"))
}

/// A thread of the pool: runs its first job, then each that it is given while it is idle.
fn work(first: Option<Job>, tx: &Sender<Job>, rx: &Receiver<Job>) {
    enter();
    let mut next = first;
    while let Some(job) = next.take() {
        job();
        RUNNING.fetch_sub(1, Ordering::AcqRel);
        let mut idle = IDLE.lock().unwrap_or_else(PoisonError::into_inner);
        if idle.len() >= KEPT {
            return;
        }
        idle.push(tx.clone());
        drop(idle);
        next = rx.recv().ok();
    }
}
