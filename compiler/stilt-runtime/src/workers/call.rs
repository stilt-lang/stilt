//! A call of `std.par` split into parts: which parts threads have taken, which have ended and
//! how, and the calling thread's side, which finishes them in order.

use std::marker::PhantomData;
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, PoisonError};

use crate::watch::Ended;

/// How a part ended the program, which its caller ends the program with in its turn.
#[derive(Debug)]
pub(crate) enum Ending {
    /// A panic of this kind at this location, with this detail (`crate::panic`).
    Panic { loc: u64, kind: u64, detail: String },
    /// Running out of a resource (`crate::entry::fatal`).
    Fatal(String),
    /// A watched run's stop, or another end (`crate::watch::end`).
    Ended(Ended),
}

impl Ending {
    /// Ends the program on the current thread as the part ended it.
    fn replay(self) -> ! {
        match self {
            Self::Panic { loc, kind, detail } => crate::panic::panic(loc, kind, &detail),
            Self::Fatal(reason) => crate::entry::fatal(&reason),
            Self::Ended(ended) => crate::watch::end(ended),
        }
    }
}

/// A part that runs, or that no thread has taken.
const RUNNING: u8 = 0;
/// A part that ran to its end.
const DONE: u8 = 1;
/// A part that ended the program.
const ENDED: u8 = 2;

/// The bit of [`Job::next`] set once no worker may take a part: a part has ended the program,
/// or the caller is done with the call.
const STOP: usize = 1 << (usize::BITS - 1);

/// A call's parts, which its caller and the workers share.
pub(crate) struct Job {
    parts: usize,
    /// The next part that no thread has taken, and [`STOP`]: one word, so that a part is taken
    /// before the call stops or not at all.
    next: AtomicUsize,
    states: Box<[AtomicU8]>,
    endings: Mutex<Vec<(usize, Ending)>>,
    lock: Mutex<()>,
    changed: Condvar,
    /// What runs a part: a closure that the caller keeps until every part a thread took has
    /// ended, and the code that calls it.
    run: *const (),
    call: unsafe fn(*const (), usize),
    /// Whether the caller computes a lazy value, as each part then does (polymorphism.lazy-values).
    lazy: bool,
}

/// Calls the closure `run` points to on part `k`.
///
/// # Safety
///
/// `run` points to a live `F`.
unsafe fn call_part<F: Fn(usize) + Sync>(run: *const (), k: usize) {
    // SAFETY: as the caller guarantees.
    unsafe { (*run.cast::<F>())(k) }
}

// SAFETY: `run` points to a `Sync` closure that outlives every use (`Call`), and the rest is
// shared through atomics and mutexes.
unsafe impl Send for Job {}
// SAFETY: as above.
unsafe impl Sync for Job {}

impl Job {
    /// Runs part `k`, which the current thread took, as part of the computation of a lazy
    /// value when the caller computes one.
    pub(super) fn run(&self, k: usize) {
        // SAFETY: the caller keeps the closure until every part taken has ended (`Call`).
        crate::std_lazy::computing_as(self.lazy, || unsafe { (self.call)(self.run, k) });
    }

    /// Whether a worker may still take a part.
    pub(super) fn open(&self) -> bool {
        let n = self.next.load(Ordering::SeqCst);
        n & STOP == 0 && n < self.parts
    }

    /// Takes the next part for a worker, if there is one.
    pub(super) fn take(&self) -> Option<usize> {
        self.next
            .try_update(Ordering::SeqCst, Ordering::SeqCst, |n| {
                (n & STOP == 0 && n < self.parts).then_some(n + 1)
            })
            .ok()
    }

    /// Lets no worker take another part, its caller having ended the program.
    pub(super) fn close(&self) {
        self.stop();
    }

    /// Lets no worker take another part, and tells how many threads have taken.
    fn stop(&self) -> usize {
        (self.next.fetch_or(STOP, Ordering::SeqCst) & !STOP).min(self.parts)
    }

    /// Marks part `k` as `state`, and wakes its caller.
    fn set(&self, k: usize, state: u8) {
        self.states[k].store(state, Ordering::Release);
        let _held = self.lock.lock().unwrap_or_else(PoisonError::into_inner);
        self.changed.notify_all();
    }

    /// Says part `k` ran to its end.
    pub(super) fn done(&self, k: usize) {
        self.set(k, DONE);
    }

    /// Says part `k` ended the program as `ending` says.
    pub(super) fn end(&self, k: usize, ending: Ending) {
        self.stop();
        self.endings
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push((k, ending));
        self.set(k, ENDED);
    }

    /// Waits until part `k` has ended, one way or another, and tells how.
    fn wait(&self, k: usize) -> u8 {
        for _ in 0..1000 {
            let state = self.states[k].load(Ordering::Acquire);
            if state != RUNNING {
                return state;
            }
            std::hint::spin_loop();
        }
        let mut held = self.lock.lock().unwrap_or_else(PoisonError::into_inner);
        loop {
            let state = self.states[k].load(Ordering::Acquire);
            if state != RUNNING {
                return state;
            }
            held = self
                .changed
                .wait(held)
                .unwrap_or_else(PoisonError::into_inner);
        }
    }

    /// How part `k` ended the program.
    fn ending(&self, k: usize) -> Option<Ending> {
        let mut endings = self.endings.lock().unwrap_or_else(PoisonError::into_inner);
        let at = endings.iter().position(|(part, _)| *part == k)?;
        Some(endings.swap_remove(at).1)
    }
}

/// The caller's side of a call: it finishes the parts in order, and keeps the closure that runs
/// them alive until every part a thread took has ended.
pub(crate) struct Call<'a> {
    job: Arc<Job>,
    finished: usize,
    run: PhantomData<&'a ()>,
}

impl<'a> Call<'a> {
    /// Starts a call of `parts` parts, part `k` being `run(k)`, the calling thread keeping the
    /// first for itself.
    pub(crate) fn start<F: Fn(usize) + Sync>(parts: usize, run: &'a F) -> Self {
        let job = Arc::new(Job {
            parts,
            next: AtomicUsize::new(1),
            states: (0..parts).map(|_| AtomicU8::new(RUNNING)).collect(),
            endings: Mutex::new(Vec::new()),
            lock: Mutex::new(()),
            changed: Condvar::new(),
            run: std::ptr::from_ref(run).cast(),
            call: call_part::<F>,
            lazy: crate::std_lazy::computing(),
        });
        super::publish(&job, parts);
        Self {
            job,
            finished: 0,
            run: PhantomData,
        }
    }

    /// Finishes part `k`, the first not finished yet: runs it on the calling thread if no
    /// worker has taken it, and otherwise waits for it, then ends the program as the part ended
    /// it, if it did, every part before it having run to its end (par.panics).
    pub(crate) fn finish(&mut self, k: usize) {
        assert_eq!(k, self.finished, "the parts of a call finish in order");
        self.finished = k + 1;
        let job = &self.job;
        // Part 0 is the caller's, and a part no worker took is the caller's, even once a later
        // part has stopped the call.
        let mine = k == 0
            || job
                .next
                .try_update(Ordering::SeqCst, Ordering::SeqCst, |n| {
                    (n & !STOP == k).then_some(n + 1)
                })
                .is_ok();
        if mine {
            job.run(k);
            job.states[k].store(DONE, Ordering::Relaxed);
            return;
        }
        if job.wait(k) == ENDED {
            let ending = job.ending(k).expect("an ended part says how");
            ending.replay();
        }
    }
}

impl Drop for Call<'_> {
    /// Waits for every part a thread took, so that no thread runs `run` once the caller has let
    /// it go.
    fn drop(&mut self) {
        let job = &self.job;
        let taken = job.stop();
        for k in self.finished..taken {
            job.wait(k);
        }
        super::withdraw(job);
    }
}
