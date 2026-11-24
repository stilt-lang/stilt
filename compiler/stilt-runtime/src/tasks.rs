//! Tasks on threads (tasks.same-output-under-every-handler and tasks.with-waits): what a thread
//! that runs a task's code knows of its place in the run, and what keeps the run's output, reads,
//! panics and ends in the order of the sequential run, which is its meaning (tasks.sequential-run).
//!
//! A run's first task started on a thread makes it a [`Run`]: a tree of segments, one per task
//! (`segments`), and the thread that started it takes the root. Every thread that runs code of
//! the run knows its segment ([`Here`]): its writes go through it ([`out`]), and at a point it
//! can't take back, a read of standard input, a panic or an `exit`, it waits for its [`turn`].
//! Code that the sequential run never reaches, a cancelled task's or a scope's function's past
//! the raise that ends it, stops for good at such a point instead ([`abandon`]), with what it
//! holds: nothing it does from then on is seen.
//!
//! A `with` of `task.threads()` counts the tasks started under it in a [`Group`], and ends once
//! each has ended (tasks.with-waits); a task's thread runs under the same handler, in the same
//! group. Neither a group nor a scope waits for a task, or a scope's function, that a cut or a
//! cancel put out of the sequential run (tasks.scope-failure and tasks.scope-that-escapes): it is
//! [`Waited`] no more, and its thread goes on until it ends or stops, unseen. While such threads
//! hold what their frames hold, the check at exit that every count is back to zero can't be made,
//! and isn't ([`unreached_threads`]; ).

mod order;
mod segments;
mod threads;

use std::cell::{Cell, RefCell};
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, MutexGuard, PoisonError};

pub(crate) use order::{holding, release, symbols};
pub(crate) use segments::SegId;
use segments::{CLOSED, FRONT, Tree};
pub(crate) use threads::running as running_jobs;

use crate::io::Kind;
use crate::watch::Watched;

/// A run whose tasks run on threads: its tree of segments, and what tells its threads that it
/// changed.
#[derive(Debug)]
pub(crate) struct Run {
    tree: Mutex<Tree>,
    changed: Condvar,
}

/// The tree of a run, locked, which tells the fault handler not to wait while the lock is held.
pub(crate) struct Locked<'a>(Option<MutexGuard<'a, Tree>>);

impl std::ops::Deref for Locked<'_> {
    type Target = Tree;
    fn deref(&self) -> &Tree {
        self.0.as_ref().expect("a locked tree")
    }
}

impl std::ops::DerefMut for Locked<'_> {
    fn deref_mut(&mut self) -> &mut Tree {
        self.0.as_mut().expect("a locked tree")
    }
}

impl Drop for Locked<'_> {
    fn drop(&mut self) {
        IN_TREE.set(false);
    }
}

impl Run {
    pub(crate) fn lock(&self) -> Locked<'_> {
        let guard = self.tree.lock().unwrap_or_else(PoisonError::into_inner);
        IN_TREE.set(true);
        Locked(Some(guard))
    }

    /// Waits until the tree changes, unless the watched run has ended then, when the thread
    /// stops for good (`crate::watch`).
    pub(crate) fn wait<'a>(&'a self, mut locked: Locked<'a>) -> Locked<'a> {
        let guard = locked.0.take().expect("a locked tree");
        IN_TREE.set(false);
        let guard = crate::watch::block(|| self.changed.wait(guard));
        drop(guard);
        crate::watch::unblock();
        self.lock()
    }

    /// Tells the threads that wait that the tree changed.
    pub(crate) fn changed(&self) {
        self.changed.notify_all();
    }
}

/// Where the current thread's code runs: its run, its segment, and the group that the tasks it
/// starts outside every `with` of its own join, when it runs a task under `task.threads()`.
#[derive(Debug, Clone)]
pub(crate) struct Here {
    pub(crate) run: Arc<Run>,
    pub(crate) seg: SegId,
    pub(crate) group: Option<Arc<Group>>,
    turn: Arc<AtomicU8>,
}

thread_local! {
    static HERE: RefCell<Option<Here>> = const { RefCell::new(None) };
    /// What tells those that wait for the current thread's job that it stopped for good.
    static ABANDON: RefCell<Option<Box<dyn FnOnce()>>> = const { RefCell::new(None) };
    /// The threads that detached code which ended on this one gives back once its job, and
    /// what it ended with, are gone ([`Waited::ended`]).
    static OWED: Cell<usize> = const { Cell::new(0) };
    /// The turn of the current thread's segment, which the fault handler reads.
    static TURN: Cell<*const AtomicU8> = const { Cell::new(std::ptr::null()) };
    /// Whether the current thread holds a run's lock.
    static IN_TREE: Cell<bool> = const { Cell::new(false) };
}

/// Where the current thread's code runs, if a task of its run runs on a thread.
pub(crate) fn here() -> Option<Here> {
    HERE.with_borrow(Clone::clone)
}

/// Makes `here` the current thread's place, and gives the one it replaces.
fn set_here(here: Option<Here>) -> Option<Here> {
    TURN.set(
        here.as_ref()
            .map_or(std::ptr::null(), |h| Arc::as_ptr(&h.turn)),
    );
    HERE.replace(here)
}

/// The current thread's place, made the root of a new run if it has none.
pub(crate) fn here_or_root() -> Here {
    if let Some(here) = here() {
        return here;
    }
    let (tree, root) = Tree::new();
    let turn = tree.turn_flag(root);
    let run = Arc::new(Run {
        tree: Mutex::new(tree),
        changed: Condvar::new(),
    });
    let here = Here {
        run,
        seg: root,
        group: None,
        turn,
    };
    set_here(Some(here.clone()));
    here
}

impl Here {
    /// The place of a task that the current code starts now, which blocks the `when`s after
    /// it if `blocks` (`order`), with its tasks joining `group`.
    pub(crate) fn spawn(&self, blocks: bool, group: Option<Arc<Group>>) -> Here {
        let mut tree = self.run.lock();
        let seg = tree.spawn(self.seg, blocks);
        let turn = tree.turn_flag(seg);
        drop(tree);
        self.run.changed();
        Here {
            run: Arc::clone(&self.run),
            seg,
            group,
            turn,
        }
    }

    /// Ends the segment: its code has ended.
    pub(crate) fn end(&self) {
        self.run.lock().end(self.seg);
        self.run.changed();
    }

    /// Whether what its code writes is dropped, as the sequential run never runs it.
    pub(crate) fn closed(&self) -> bool {
        self.run.lock().closed(self.seg)
    }
}

/// Does a write of the current thread through its segment, and tells whether it did: without
/// a run, the caller writes it itself.
pub(crate) fn out(kind: Kind, bytes: &[u8]) -> bool {
    let Some(here) = here() else { return false };
    here.run.lock().write(here.seg, kind, bytes);
    true
}

/// Waits until the current thread's segment is at the front of its run, so that what it does
/// next happens where the sequential run does it, or stops the thread for good if the
/// sequential run never gets there.
pub(crate) fn turn() {
    let Some(here) = here() else { return };
    let mut tree = here.run.lock();
    loop {
        match tree.turn(here.seg) {
            FRONT => return,
            CLOSED => {
                drop(tree);
                abandon();
            }
            _ => tree = here.run.wait(tree),
        }
    }
}

/// Stops the current thread for good, at a point of code that the sequential run never
/// reaches, once those that wait for its job are told, which lets go of what the job holds
/// apart from its frames and adds the thread's counts to the totals first.
pub(crate) fn abandon() -> ! {
    match ABANDON.take() {
        Some(tell) => tell(),
        None => crate::pool::flush(),
    }
    crate::watch::parked();
    loop {
        std::thread::park();
    }
}

#[cfg(not(target_family = "wasm"))]
/// At a stack overflow, in the fault handler: waits, without a lock, for the current thread's
/// turn, and stops it for good if it never comes. A thread that holds its run's lock doesn't
/// wait, since no turn would change.
pub(crate) fn fault_turn() {
    let turn = TURN.get();
    if turn.is_null() || IN_TREE.get() {
        return;
    }
    // SAFETY: the flag lives as long as the thread's `Here`, which outlives its code.
    let turn = unsafe { &*turn };
    loop {
        match turn.load(Ordering::Acquire) {
            FRONT => return,
            CLOSED => loop {
                // SAFETY: `pause` is async-signal-safe.
                unsafe { libc::pause() };
            },
            _ => {
                let pause = libc::timespec {
                    tv_sec: 0,
                    tv_nsec: 1_000_000,
                };
                // SAFETY: `nanosleep` is async-signal-safe.
                unsafe { libc::nanosleep(&raw const pause, std::ptr::null_mut()) };
            }
        }
    }
}

/// A handler of `async`, as a `with` installs it: `task.sequential()`, or `task.threads()` with
/// the tasks started under it.
#[derive(Debug, Clone)]
pub(crate) enum Async {
    Sequential,
    Threads(Arc<Group>),
}

/// The tasks started under a `with` of `task.threads()`, which ends once each has ended.
#[derive(Debug, Default)]
pub(crate) struct Group {
    live: Mutex<usize>,
    ended: Condvar,
}

impl Group {
    pub(crate) fn join(&self) {
        *self.live.lock().unwrap_or_else(PoisonError::into_inner) += 1;
    }

    pub(crate) fn leave(&self) {
        let mut live = self.live.lock().unwrap_or_else(PoisonError::into_inner);
        *live -= 1;
        self.ended.notify_all();
    }

    /// Waits until every task of the group has ended, or stopped for good.
    pub(crate) fn wait(&self) {
        let live = self.live.lock().unwrap_or_else(PoisonError::into_inner);
        drop(crate::watch::block(|| {
            self.ended.wait_while(live, |live| *live > 0)
        }));
        crate::watch::unblock();
    }
}

/// The group that a task the current code starts joins, running on a thread: that of the
/// innermost `with` of `async`, or the one the thread's task runs under, if that handler is
/// `task.threads()`. A task started inside a `when`'s block runs where it starts, as in the
/// sequential run.
pub(crate) fn group() -> Option<Arc<Group>> {
    if holding() {
        return None;
    }
    match crate::effects::innermost_async() {
        Some(Async::Threads(group)) => Some(group),
        Some(Async::Sequential) => None,
        None => here().and_then(|h| h.group),
    }
}

/// Whether the current code is code that the sequential run never reaches, which starts no
/// task.
pub(crate) fn unreached() -> bool {
    here().is_some_and(|h| h.closed())
}

/// The threads that code the sequential run never reaches occupies: detached and still running,
/// or stopped for good with what their frames hold.
static UNREACHED: AtomicUsize = AtomicUsize::new(0);

/// How many threads code that the sequential run never reaches occupies, which keeps the check
/// at exit from being made.
pub(crate) fn unreached_threads() -> usize {
    UNREACHED.load(Ordering::Acquire)
}

/// Whether a task, or a scope's function, is still waited for.
const RUNNING: u8 = 0;
const ENDED: u8 = 1;
const DETACHED: u8 = 2;

/// A task, or a scope's function, that a group or a scope waits for, until it ends or stops,
/// or until a cut or a cancel of its segment puts it out of the sequential run, when its waiter
/// is told at once and waits for it no more (tasks.scope-that-escapes).
#[derive(Debug, Clone)]
pub(crate) struct Waited(Arc<AtomicU8>);

impl Waited {
    /// Waits for the code of `place`, before it starts: `leave` tells the waiter it left, once.
    pub(crate) fn new(place: &Here, leave: impl FnOnce() + Send + 'static) -> Self {
        let state = Arc::new(AtomicU8::new(RUNNING));
        let mine = Arc::clone(&state);
        let detach = Box::new(move || {
            if mine
                .compare_exchange(RUNNING, DETACHED, Ordering::AcqRel, Ordering::Acquire)
                .is_ok()
            {
                UNREACHED.fetch_add(1, Ordering::AcqRel);
                leave();
            }
        });
        place.run.lock().on_close(place.seg, detach);
        Self(state)
    }

    /// Its code ended: whether its waiter still waits for it, and so must be told. One that a
    /// cut detached keeps what it ended with to let go of, and gives back its thread only once
    /// its job is over ([`launch`]), so that the check at exit never runs while it still holds
    /// what it ended with.
    pub(crate) fn ended(&self) -> bool {
        if self.0.swap(ENDED, Ordering::AcqRel) == DETACHED {
            OWED.set(OWED.get() + 1);
            return false;
        }
        true
    }

    /// Its code stopped for good, keeping what its frames hold: whether its waiter still waits
    /// for it, and so must be told.
    pub(crate) fn stopped(&self) -> bool {
        if self.0.swap(ENDED, Ordering::AcqRel) == DETACHED {
            return false;
        }
        UNREACHED.fetch_add(1, Ordering::AcqRel);
        true
    }
}

/// Whether a task may start on a thread now; one that may must be given to [`launch`].
pub(crate) fn reserve() -> bool {
    threads::reserve()
}

/// Runs `body` as the code of `place` on a thread of the pool, after [`reserve`], with the
/// current thread's watched run, or on the current thread when no thread starts. `abandoned`
/// tells those that wait for it if it stops for good.
pub(crate) fn launch(
    place: Here,
    abandoned: Box<dyn FnOnce() + Send>,
    body: Box<dyn FnOnce() + Send>,
) {
    let watched = Watched::current();
    watched.job(false);
    let job: threads::Job = Box::new(move || {
        let watched = watched.install();
        let outer = set_here(Some(place));
        let tell = ABANDON.replace(Some(abandoned));
        body();
        ABANDON.set(tell);
        let owed = OWED.replace(0);
        if owed > 0 {
            UNREACHED.fetch_sub(owed, Ordering::AcqRel);
        }
        set_here(outer);
        watched.install().job(true);
    });
    if let Err(job) = threads::start(job) {
        job();
    }
}
