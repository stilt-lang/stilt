//! The time a span of the work takes on an idle reference machine, as its cycles at the reference
//! machine's clock or its wall time, whichever is less ([`stilt_meter::Counts::idle_time`]; Goals,
//! Timing): this process's, for what the harness does itself, and those of the processes it asks,
//! a language server, a REPL or an engine, read by their pids, so that other programs on the
//! machine leave the time nearly as it is. A process that can't be read, as one that ended within
//! the span, leaves the span timed by the wall clock.

use std::path::Path;
use std::process::Command;
use std::time::{Duration, Instant};

use stilt_meter::Counts;

/// A span's start.
#[derive(Debug)]
pub(crate) struct Clock {
    pids: Vec<u32>,
    start: Option<Counts>,
    wall: Instant,
}

impl Clock {
    /// Starts timing the work of this process.
    pub(crate) fn own() -> Self {
        Self::of(&[std::process::id()])
    }

    /// Starts timing the work of a client and the engine of the program at `root`, which the
    /// client asks: the wall clock when no engine holds the program, since the work it does
    /// would go uncounted.
    pub(crate) fn of_client(client: u32, root: &Path) -> Self {
        match engine_of(root) {
            Some(engine) => Self::of(&[client, engine]),
            None => Self {
                pids: Vec::new(),
                start: None,
                wall: Instant::now(),
            },
        }
    }

    /// Starts timing the work of the processes `pids`, all together.
    pub(crate) fn of(pids: &[u32]) -> Self {
        Self {
            pids: pids.to_vec(),
            start: counts(pids),
            wall: Instant::now(),
        }
    }

    /// The time the work took since the start.
    pub(crate) fn elapsed(&self) -> Duration {
        self.elapsed_with(Counts::ZERO)
    }

    /// The time the work took since the start, with that of `more`, the counts of a process
    /// that ran within the span and ended, which the wall clock already holds.
    pub(crate) fn elapsed_with(&self, more: Counts) -> Duration {
        let wall = self.wall.elapsed();
        match (self.start, counts(&self.pids)) {
            (Some(start), Some(now)) => now.since(start).plus(more).idle_time(wall),
            _ => wall,
        }
    }
}

fn counts(pids: &[u32]) -> Option<Counts> {
    pids.iter().try_fold(Counts::ZERO, |sum, &pid| {
        stilt_meter::of(pid).ok().map(|c| sum.plus(c))
    })
}

/// The pid of the engine that holds the program at `root`, whose command line is `stilt engine`
/// and the program's canonical path, if one runs.
fn engine_of(root: &Path) -> Option<u32> {
    let root = root.canonicalize().ok()?;
    let tail = format!(" engine {}", root.display());
    let output = Command::new("ps")
        .args(["-A", "-o", "pid=,command="])
        .output()
        .ok()?;
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .find_map(|line| {
            let (pid, command) = line.trim_start().split_once(' ')?;
            command.ends_with(&tail).then(|| pid.parse().ok()).flatten()
        })
}
