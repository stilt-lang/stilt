//! Programs that `stilt run` runs, whose code changes while they run.
//!
//! A watched run ends without ending the process: a panic, a call of `exit` or running out of
//! memory reports as usual, then leaves the program's thread waiting forever, with the objects
//! it held, and the compiler, told how the run ended, ends the process with its status. A run
//! whose values a change made meaningless is stopped: the compiler sets [`STOP`], and compiled
//! code, which polls it on entering a function and on each loop's back edge, ends the run at
//! its next poll.

use std::cell::RefCell;
use std::sync::atomic::{AtomicBool, AtomicIsize, AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex, PoisonError};
use std::time::Duration;

mod results;
mod threads;

pub use results::{Evaluated, Note, Outcome, Tested};
pub(crate) use threads::{Watched, block, parked, unblock};

use crate::entry::{Entry, Program, enter, prepare, run_main};
use crate::prop::Tape;
use crate::{io, object, text};

/// Nonzero while the running program must stop at its next poll.
pub(crate) static STOP: AtomicU64 = AtomicU64::new(0);

/// How a watched run ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ended {
    /// With this exit status (program.exit-statuses).
    Status(i32),
    /// Stopped before its end, by [`Running::stop`].
    Stopped,
    /// A test's entry returned, telling whether the test passed ([`test`]).
    Tested(bool),
}

#[derive(Debug, Default)]
struct Shared {
    ended: Mutex<Option<Ended>>,
    changed: Condvar,
    /// How a run of a property's closure ended, when it ran one.
    outcome: Mutex<Option<Outcome>>,
    /// Whether the run ended with a panic, rather than a call of `exit`.
    panicked: AtomicBool,
    /// Whether the run is a test's, whose panic report is kept for its result, not written.
    capture: AtomicBool,
    /// What a test said of its failure ([`stilt_rt_test_note`]).
    note: Mutex<Option<Note>>,
    /// The report of the panic that ended a test.
    report: Mutex<Option<String>>,
    /// The threads of the run that may run its code: its own, and those of its tasks, but
    /// while they wait in the runtime (`threads`).
    jobs: AtomicIsize,
}

impl Shared {
    /// Records how the run ended, a status being that of the process: 2 for a program with
    /// errors (program.programs-with-errors).
    fn finish(&self, ended: Ended) {
        let ended = match ended {
            Ended::Status(code) => Ended::Status(crate::entry::status(code)),
            other => other,
        };
        let mut slot = self.ended.lock().unwrap_or_else(PoisonError::into_inner);
        slot.get_or_insert(ended);
        self.changed.notify_all();
    }
}

thread_local! {
    /// What the thread of a watched run reports its end to: the run's own thread, and each
    /// thread that runs a task of it, which ends the run as the run's thread does.
    static WATCHED: RefCell<Option<Arc<Shared>>> = const { RefCell::new(None) };
}

/// Records the panic that ends a run of a property's closure, if the current thread runs one, whose
/// outcome then carries it instead of a report on stderr (tests.property-verdict). Tells whether it
/// did.
pub(crate) fn property_panic(kind: &str, detail: &str) -> bool {
    WATCHED.with_borrow(|shared| {
        let Some(shared) = shared else { return false };
        let mut outcome = shared
            .outcome
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        match &*outcome {
            Some(Outcome::Passed) => {
                *outcome = Some(Outcome::Panicked {
                    kind: kind.to_owned(),
                    detail: detail.to_owned(),
                });
                true
            }
            _ => false,
        }
    })
}

/// Keeps the report of the panic that ends a test, if the current thread runs one, in place of
/// writing it. Tells whether it did.
pub(crate) fn test_panic(report: &str) -> bool {
    WATCHED.with_borrow(|shared| {
        let Some(shared) = shared.as_ref().filter(|s| s.capture.load(Ordering::SeqCst)) else {
            return false;
        };
        *shared.report.lock().unwrap_or_else(PoisonError::into_inner) = Some(report.to_owned());
        true
    })
}

/// Records what the current test says of its failure: with `other` 0, the text `shown` of an
/// error it raised, and otherwise the texts of the two sides of a comparison that was false.
/// The compiler calls it from a test's entry and from a doc example's body.
///
/// # Safety
///
/// `shown` is a live string, and so is `other` when it isn't 0.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_test_note(shown: u64, other: u64) {
    // SAFETY: the caller guarantees both are live strings.
    let text = |w| unsafe { text::text(&w) }.to_owned();
    let note = if other == 0 {
        Note::Raised(text(shown))
    } else {
        Note::Compared(text(shown), text(other))
    };
    WATCHED.with_borrow(|shared| {
        if let Some(shared) = shared {
            *shared.note.lock().unwrap_or_else(PoisonError::into_inner) = Some(note);
        }
    });
}

/// Records that the run of the current thread, if it is watched, ends with a panic.
pub(crate) fn panicked() {
    WATCHED.with_borrow(|shared| {
        if let Some(shared) = shared {
            shared.panicked.store(true, Ordering::SeqCst);
        }
    });
}

/// A watched run of a program.
#[derive(Debug)]
pub struct Running {
    shared: Arc<Shared>,
}

/// Starts a watched run of a program. A stopped run keeps its objects, so a run started after
/// one was stopped mustn't check for leaks.
///
/// # Panics
///
/// Panics when the system can't start the thread the program runs on.
#[must_use]
pub fn start(program: Program) -> Running {
    let entry: Entry = program.entry;
    let check_leaks = program.check_leaks;
    prepare(program);
    let shared = Arc::new(Shared::default());
    shared.jobs.store(1, Ordering::SeqCst);
    let theirs = Arc::clone(&shared);
    crate::stacks::spawn("main", move || {
        WATCHED.set(Some(Arc::clone(&theirs)));
        let status = run_main(entry, check_leaks);
        io::flush();
        theirs.jobs.fetch_sub(1, Ordering::SeqCst);
        theirs.finish(Ended::Status(status));
    })
    .expect("a thread for the program");
    Running { shared }
}

impl Running {
    /// How the run ended, if it has.
    #[must_use]
    pub fn ended(&self) -> Option<Ended> {
        *self
            .shared
            .ended
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    /// How the run ended, waiting at most `timeout` for it to end.
    #[must_use]
    pub fn wait(&self, timeout: Duration) -> Option<Ended> {
        let slot = self
            .shared
            .ended
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        let (slot, _) = self
            .shared
            .changed
            .wait_timeout_while(slot, timeout, |ended| ended.is_none())
            .unwrap_or_else(PoisonError::into_inner);
        *slot
    }

    /// Stops the run at its next poll, and the threads of a run that has ended, such as a
    /// worker of `std.par` still running a part of the call whose other part panicked, waiting
    /// at most `timeout` for them, and tells whether the run has ended with no thread left to
    /// run its code. A run that never polls, such as one in a loop of no calls or waiting for
    /// input, goes on.
    #[must_use]
    pub fn stop(&self, timeout: Duration) -> bool {
        let deadline = std::time::Instant::now() + timeout;
        STOP.store(1, Ordering::SeqCst);
        let ended = self.ended().is_some() || self.wait(timeout).is_some();
        // The workers still running parts of the run's calls of `std.par`, and the threads of
        // its tasks, stop at their next poll too, rather than run on for the run that ended.
        crate::workers::settle(deadline);
        let quiet = self.settle(deadline);
        STOP.store(0, Ordering::SeqCst);
        // A thread of the run that goes on may still change the counts of shared objects, so
        // no collection of cycles may run in this process again.
        if !(ended && quiet) {
            crate::object::forsake();
        }
        ended && quiet
    }
}

/// What a mutex holds, taken.
fn kept<T>(slot: &Mutex<Option<T>>) -> Option<T> {
    slot.lock().unwrap_or_else(PoisonError::into_inner).take()
}

/// Runs a test or doc example by its entry, on a thread of its own, as a watched run is run, and
/// tells whether it passed (program.test-results and program.running-tests): its entry gives 1 when
/// it passes, and a panic or a call of `exit` fails it, leaving the thread waiting forever with the
/// objects it held. A panic is not written but kept, with what the test said of its failure. The
/// process must be prepared by [`crate::prepare_tests`].
///
/// # Panics
///
/// Panics when the system can't start the thread the test runs on.
#[must_use]
pub fn test(entry: Entry) -> Tested {
    let shared = Arc::new(Shared::default());
    shared.capture.store(true, Ordering::SeqCst);
    let theirs = Arc::clone(&shared);
    crate::stacks::spawn("test", move || {
        WATCHED.set(Some(Arc::clone(&theirs)));
        enter();
        // SAFETY: the compiler compiled a test's entry with the signature `Entry`.
        let ended = unsafe { entry(0) };
        crate::pool::flush();
        io::flush();
        theirs.finish(Ended::Tested(ended.raised == 0 && ended.value != 0));
    })
    .expect("a thread for the test");
    let running = Running {
        shared: Arc::clone(&shared),
    };
    loop {
        if let Some(ended) = running.wait(Duration::from_secs(3600)) {
            return Tested {
                passed: ended == Ended::Tested(true),
                returned: matches!(ended, Ended::Tested(_)),
                note: kept(&shared.note),
                report: kept(&shared.report),
            };
        }
    }
}

/// Runs a property's closure on the values its entry reads from `tape`, on a thread of its own,
/// as [`test`] runs a test, and tells how the run ended (tests.running-cases): its entry gives 1
/// when the closure returns `true`, and raises the text of what the closure raises; a panic
/// leaves the thread waiting forever, with the objects it held. The process must be prepared by
/// [`crate::prepare_tests`].
///
/// # Panics
///
/// Panics when the system can't start the thread the run runs on.
#[must_use]
pub fn property(entry: Entry, tape: &mut Tape) -> Outcome {
    let shared = Arc::new(Shared::default());
    // Until the run ends otherwise, a panic is what ends it.
    *shared
        .outcome
        .lock()
        .unwrap_or_else(PoisonError::into_inner) = Some(Outcome::Passed);
    let theirs = Arc::clone(&shared);
    let tape = std::ptr::from_mut(tape) as u64;
    let thread = crate::stacks::spawn("property", move || {
        WATCHED.set(Some(Arc::clone(&theirs)));
        enter();
        // SAFETY: the compiler compiled a property's entry with the signature `Entry`, and
        // the tape outlives the run, which alone uses it.
        let ended = unsafe { entry(tape) };
        io::flush();
        let outcome = if ended.raised != 0 {
            // SAFETY: the entry raises the error's text as a string it owns.
            let shown = unsafe { text::text(&ended.value) }.to_owned();
            // SAFETY: as above.
            unsafe { object::drop(ended.value) };
            Outcome::Raised(shown)
        } else if ended.value != 0 {
            Outcome::Passed
        } else {
            Outcome::False
        };
        *theirs
            .outcome
            .lock()
            .unwrap_or_else(PoisonError::into_inner) = Some(outcome);
        crate::pool::flush();
        theirs.finish(Ended::Tested(true));
    })
    .expect("a thread for the property");
    let running = Running {
        shared: Arc::clone(&shared),
    };
    loop {
        if let Some(ended) = running.wait(Duration::from_secs(3600)) {
            if ended == Ended::Tested(true) {
                let _ = thread.join();
            }
            break;
        }
    }
    let outcome = shared
        .outcome
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take();
    match outcome {
        Some(outcome) if matches!(running.ended(), Some(Ended::Tested(true))) => outcome,
        Some(Outcome::Panicked { kind, detail }) => Outcome::Panicked { kind, detail },
        // A call of `exit`, which a property can't make, since it performs `io`.
        _ => Outcome::Panicked {
            kind: "exit".to_owned(),
            detail: String::new(),
        },
    }
}

/// Runs an input's entry on the frame that `frame` points to, on a thread of its own, as
/// [`test`] runs a test: a raise or a panic ends only the input, whose thread then waits
/// forever with the objects it held (`crate::session`).
///
/// # Panics
///
/// Panics when the system can't start the thread the input runs on.
pub(crate) fn run_input(entry: Entry, frame: u64) -> Evaluated {
    let shared = Arc::new(Shared::default());
    let theirs = Arc::clone(&shared);
    let result = Arc::new(Mutex::new(None));
    let ours = Arc::clone(&result);
    let thread = crate::stacks::spawn("input", move || {
        WATCHED.set(Some(Arc::clone(&theirs)));
        enter();
        // SAFETY: the compiler compiled an input's entry with the signature `Entry`, and
        // the frame outlives the run, which alone uses it.
        let ended = unsafe { entry(frame) };
        io::flush();
        // SAFETY: the entry gives, or raises, a string it owns.
        let text = unsafe { text::text(&ended.value) }.to_owned();
        // SAFETY: as above.
        unsafe { object::drop(ended.value) };
        let evaluated = if ended.raised == 0 {
            Evaluated::Value(text)
        } else {
            Evaluated::Raised(text)
        };
        *ours.lock().unwrap_or_else(PoisonError::into_inner) = Some(evaluated);
        crate::pool::flush();
        theirs.finish(Ended::Tested(true));
    })
    .expect("a thread for the input");
    let running = Running {
        shared: Arc::clone(&shared),
    };
    let ended = loop {
        if let Some(ended) = running.wait(Duration::from_secs(3600)) {
            break ended;
        }
    };
    if ended == Ended::Tested(true) {
        let _ = thread.join();
    }
    let returned = result.lock().unwrap_or_else(PoisonError::into_inner).take();
    match (ended, returned) {
        (Ended::Tested(_), Some(evaluated)) => evaluated,
        (Ended::Status(code), _) if !shared.panicked.load(Ordering::SeqCst) => {
            Evaluated::Ended(code)
        }
        _ => Evaluated::Panicked,
    }
}

/// Ends the running program, once its output is written: a watched run's thread waits forever,
/// and any other run ends the process with the status.
pub(crate) fn end(ended: Ended) -> ! {
    crate::workers::end(|| crate::workers::Ending::Ended(ended));
    io::flush();
    match WATCHED.with_borrow(Clone::clone) {
        Some(shared) => {
            // Counted out before the end is told, as a run that returns is: the caller frees
            // the run's code once no thread may run it, which it checks when told.
            parked();
            shared.finish(ended);
            threads::park()
        }
        None => crate::entry::exit_process(crate::entry::status(match ended {
            Ended::Status(code) => code,
            Ended::Stopped | Ended::Tested(_) => 0,
        })),
    }
}

/// Ends a watched run that must stop. Compiled code calls it when [`STOP`] is set.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_poll() {
    if STOP.load(Ordering::SeqCst) != 0 {
        end(Ended::Stopped);
    }
}

/// The functions and data of this module that compiled code reaches, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    let mut all = crate::exports![stilt_rt_poll, stilt_rt_test_note];
    all.push(("stilt_rt_stop", std::ptr::from_ref(&STOP).cast()));
    all
}
