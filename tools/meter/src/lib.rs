//! What a process costs, counted by the processor: the instructions its threads retire, the cycles
//! they run and their CPU time (Goals, Timing).
//!
//! Other processes on the machine change a program's wall time severalfold, and its CPU time by
//! half again. They don't change the instructions it retires, and change its cycles by what the
//! programs contend for, the caches and the memory, and by where the system runs it: under load it
//! moves a program to the efficiency cores, which take more cycles for the same instructions. On
//! the reference machine, under twice as many busy loops as it has cores, the fastest of five runs
//! of a Rust benchmark took 3.1 to 3.8 times its wall time, 1.5 to 1.7 times its CPU time, 1.03 to
//! 1.24 times its cycles, and 1.000 times its instructions and its cycles on a performance core.
//!
//! So a goal whose target is a time or a speed is judged on the cycles the work would run on the
//! performance cores, which count what the processor spends on memory as time does
//! ([`Counts::performance_cycles`]), converted to time at [`REFERENCE_CLOCK`], or on the wall
//! time when that is less, as for work spread over several cores ([`Counts::idle_time`]). Under
//! load that errs on the strict side. Instructions are reported beside them, as the steadiest
//! measure of the work. macOS counts all of these for every process; on Linux, where a process's
//! counters need the kernel's leave, the meter gives the CPU time alone.

#![warn(missing_docs)]

use std::io::{self, Read};
use std::process::{Child, Command, Output};
use std::thread::JoinHandle;
use std::time::Duration;

#[cfg(target_os = "linux")]
mod linux;
#[cfg(target_os = "macos")]
mod macos;
mod wait;

#[cfg(target_os = "linux")]
use linux as system;
#[cfg(target_os = "macos")]
use macos as system;

/// The cycles that a performance core of the reference machine, an Apple M4, runs in a second of
/// CPU time, as single-threaded Rust benchmarks measure it on an idle machine: 3.8 to 4.0
/// billion. A count of cycles at this clock is the time the work takes there.
pub const REFERENCE_CLOCK: f64 = 4.0e9;

/// What a process has cost so far, or what a span of its work cost.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Counts {
    /// The instructions that its threads retired, where the system counts them.
    pub instructions: Option<u64>,
    /// The cycles that its threads ran, where the system counts them.
    pub cycles: Option<u64>,
    /// What its threads retired and ran on the performance cores alone, where the system counts
    /// it.
    pub performance: Option<Performance>,
    /// The time its threads ran, in user and system mode.
    pub cpu: Duration,
}

/// The instructions that a process's threads retired on the performance cores, and the cycles
/// they ran there.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Performance {
    /// The instructions retired on the performance cores.
    pub instructions: u64,
    /// The cycles run on the performance cores.
    pub cycles: u64,
}

impl Counts {
    /// Nothing spent, every count kept: what a sum of counts starts from. A sum with counts that
    /// lack one lacks it.
    pub const ZERO: Counts = Counts {
        instructions: Some(0),
        cycles: Some(0),
        performance: Some(Performance {
            instructions: 0,
            cycles: 0,
        }),
        cpu: Duration::ZERO,
    };

    /// What was spent between `earlier` and these counts, of the same process.
    #[must_use]
    pub fn since(self, earlier: Counts) -> Counts {
        Counts {
            instructions: both(self.instructions, earlier.instructions, u64::saturating_sub),
            cycles: both(self.cycles, earlier.cycles, u64::saturating_sub),
            performance: pair(self.performance, earlier.performance, u64::saturating_sub),
            cpu: self.cpu.saturating_sub(earlier.cpu),
        }
    }

    /// What two processes, or two spans, cost together.
    #[must_use]
    pub fn plus(self, other: Counts) -> Counts {
        Counts {
            instructions: both(self.instructions, other.instructions, u64::saturating_add),
            cycles: both(self.cycles, other.cycles, u64::saturating_add),
            performance: pair(self.performance, other.performance, u64::saturating_add),
            cpu: self.cpu + other.cpu,
        }
    }

    /// The cycles the work would run on the performance cores: those it ran there, scaled by
    /// all the instructions it retired over those it retired there. A program that the system
    /// moved to the efficiency cores for part of its run is then counted as if it had stayed,
    /// as on an idle machine. Work that retired nothing on a performance core counts its cycles.
    #[must_use]
    #[allow(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        clippy::cast_precision_loss,
        reason = "a count of cycles fits a double's 53 bits for 26 days, and the scale is at least 1"
    )]
    pub fn performance_cycles(self) -> Option<u64> {
        match (self.performance, self.instructions) {
            (Some(p), Some(all)) if p.instructions > 0 => {
                let scale = all as f64 / p.instructions as f64;
                Some((p.cycles as f64 * scale.max(1.0)) as u64)
            }
            _ => self.cycles,
        }
    }

    /// The time the work takes on the reference machine: its cycles on the performance cores
    /// at [`REFERENCE_CLOCK`] where they are counted, and its CPU time where they aren't. Work
    /// that ran on several threads at once counts each thread's cycles, so this is the time it
    /// would take on one core, which is at least its time on all of them.
    #[must_use]
    #[allow(
        clippy::cast_precision_loss,
        reason = "cycles fit a double's 53 bits for 26 days"
    )]
    pub fn time(self) -> Duration {
        match self.performance_cycles() {
            Some(cycles) => Duration::from_secs_f64(cycles as f64 / REFERENCE_CLOCK),
            None => self.cpu,
        }
    }

    /// The time the work takes on an idle reference machine, from these counts and the wall
    /// time it took: the lesser of the two. Each is at least that time for work that computes
    /// rather than waits. The wall time is, since other programs only slow the work, and the
    /// cycles are, since they count every thread's work, which is at least the time that work
    /// spans. So work on one core under load is timed by its cycles, which other programs barely
    /// change, and work spread over cores on an idle machine by its wall time.
    #[must_use]
    pub fn idle_time(self, wall: Duration) -> Duration {
        self.time().min(wall)
    }
}

fn both(a: Option<u64>, b: Option<u64>, f: fn(u64, u64) -> u64) -> Option<u64> {
    Some(f(a?, b?))
}

fn pair(
    a: Option<Performance>,
    b: Option<Performance>,
    f: fn(u64, u64) -> u64,
) -> Option<Performance> {
    let (a, b) = (a?, b?);
    Some(Performance {
        instructions: f(a.instructions, b.instructions),
        cycles: f(a.cycles, b.cycles),
    })
}

/// What the process `pid` has cost so far, all its threads together, whether it runs or has
/// ended and waits to be reaped.
///
/// # Errors
///
/// When no such process exists, or the system won't tell.
pub fn of(pid: u32) -> io::Result<Counts> {
    system::counts(pid)
}

/// What this process has cost so far.
///
/// # Errors
///
/// When the system won't tell.
pub fn own() -> io::Result<Counts> {
    of(std::process::id())
}

/// Runs `command` to its end, as [`Command::output`] does, and gives what it cost, read once it
/// has ended and before it is reaped. Its children aren't counted.
///
/// # Errors
///
/// When the command can't start, or its end or its counts can't be read.
pub fn run(command: &mut Command) -> io::Result<(Output, Counts)> {
    command
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    let mut child = command.spawn()?;
    let stdout = drain(child.stdout.take());
    let stderr = drain(child.stderr.take());
    let counts = ended(&child).and_then(|()| of(child.id()));
    let status = child.wait()?;
    let output = Output {
        status,
        stdout: joined(stdout)?,
        stderr: joined(stderr)?,
    };
    Ok((output, counts?))
}

/// Waits until `child` has ended, leaving it to be reaped.
fn ended(child: &Child) -> io::Result<()> {
    wait::until_ended(child.id())
}

fn drain<R: Read + Send + 'static>(pipe: Option<R>) -> JoinHandle<io::Result<Vec<u8>>> {
    std::thread::spawn(move || {
        let mut bytes = Vec::new();
        if let Some(mut pipe) = pipe {
            pipe.read_to_end(&mut bytes)?;
        }
        Ok(bytes)
    })
}

fn joined(handle: JoinHandle<io::Result<Vec<u8>>>) -> io::Result<Vec<u8>> {
    handle
        .join()
        .map_err(|_| io::Error::other("a pipe's reader panicked"))?
}

#[cfg(test)]
mod tests;
