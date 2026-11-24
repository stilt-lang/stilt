//! The threads of a watched run beyond its own: those that run its tasks (`crate::tasks`), which
//! take on its run, and end it as its own thread does. The run counts the threads that may run
//! its code, so that once it has ended, or is stopped, its code is freed or replaced only when
//! none can: a thread is counted while it runs, and not while it waits in the runtime, from
//! which it never returns to the run's code once the run has ended, nor once it stops for good.

use std::sync::atomic::Ordering;
use std::sync::{Arc, PoisonError};
use std::time::{Duration, Instant};

use super::{Running, Shared, WATCHED};

/// The watched run the current thread belongs to, if any, which a thread that runs a task of
/// it takes on ([`Watched::install`]).
#[derive(Debug, Clone, Default)]
pub(crate) struct Watched(Option<Arc<Shared>>);

impl Watched {
    /// The current thread's.
    pub(crate) fn current() -> Self {
        Self(WATCHED.with_borrow(Clone::clone))
    }

    /// Makes it the current thread's, and gives the one it replaces.
    pub(crate) fn install(self) -> Self {
        Self(WATCHED.replace(self.0))
    }

    /// Counts a thread that starts to run the run's code, or with `ended`, one that ends.
    pub(crate) fn job(&self, ended: bool) {
        if let Some(shared) = &self.0 {
            shared
                .jobs
                .fetch_add(if ended { -1 } else { 1 }, Ordering::SeqCst);
        }
    }
}

/// Counts the current thread out of its run's, as it stops for good.
pub(crate) fn parked() {
    Watched::current().job(true);
}

/// Runs `wait`, a wait of the current thread in the runtime, during which it runs none of the
/// run's code; [`unblock`] must follow, once the wait's locks are let go.
pub(crate) fn block<T>(wait: impl FnOnce() -> T) -> T {
    Watched::current().job(true);
    wait()
}

/// The end of a wait of [`block`]: the current thread runs the run's code again, unless the run
/// has ended, when it stops for good.
pub(crate) fn unblock() {
    let watched = Watched::current();
    let over = watched.0.as_ref().is_some_and(|s| {
        s.ended
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .is_some()
    });
    if over {
        park();
    }
    watched.job(false);
}

/// Waits forever.
pub(super) fn park() -> ! {
    loop {
        std::thread::park();
    }
}

impl Running {
    /// Whether no thread of the run may run its code still, so that the code can be freed
    /// once the run has ended: none of its tasks' threads, and no worker running a part of a
    /// call of `std.par`, which goes on when a panic in another part ends the run.
    #[must_use]
    pub fn quiet(&self) -> bool {
        self.shared.jobs.load(Ordering::SeqCst) <= 0 && crate::workers::idle()
    }

    /// Waits, until `deadline` at most, for the run's threads to stop running its code, and
    /// tells whether they have.
    pub(super) fn settle(&self, deadline: Instant) -> bool {
        while !self.quiet() && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(1));
        }
        self.quiet()
    }
}
