//! A run of a program, and what its runs together measure (Goals, Timing).
//!
//! A helper runs each program: this harness, run as `stilt-bench sample`, which runs the
//! program through the meter, so that the counts are the program's own, and then reads the peak
//! resident memory of the one process it waited for, since the system reports only the largest
//! peak of all the processes a process has waited for.

use std::ffi::OsString;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::{Duration, Instant};

use nix::sys::resource::{UsageWho, getrusage};
use stilt_meter::{Counts, Performance};

/// What the helper runs.
#[derive(Debug, clap::Args)]
pub(crate) struct SampleArgs {
    /// Where to write what the program prints on stdout.
    #[arg(long)]
    stdout: PathBuf,
    /// Where to write what it prints on stderr.
    #[arg(long)]
    stderr: PathBuf,
    /// The program and its arguments.
    #[arg(last = true, required = true)]
    command: Vec<OsString>,
}

/// What one run of a program cost.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Sample {
    pub(crate) counts: Counts,
    pub(crate) wall: Duration,
    /// The peak resident memory of the run, in bytes.
    pub(crate) peak: u64,
    /// Its exit status, or 128 and the signal that ended it.
    pub(crate) status: i32,
}

impl Sample {
    /// The run's time on an idle reference machine: its cycles on the performance cores, or its
    /// wall time where that is less, as for work spread over several threads.
    pub(crate) fn time(&self) -> Duration {
        self.counts.idle_time(self.wall)
    }
}

/// The helper: runs the program, writes what it printed, and prints what the run cost.
pub(crate) fn print(args: &SampleArgs) -> ExitCode {
    let Some((program, rest)) = args.command.split_first() else {
        return ExitCode::FAILURE;
    };
    let start = Instant::now();
    let run = stilt_meter::run(Command::new(program).args(rest));
    let wall = start.elapsed();
    let (output, counts) = match run {
        Ok(run) => run,
        Err(e) => {
            eprintln!("cannot run {}: {e}", program.to_string_lossy());
            return ExitCode::FAILURE;
        }
    };
    let written = std::fs::write(&args.stdout, &output.stdout)
        .and_then(|()| std::fs::write(&args.stderr, &output.stderr));
    if let Err(e) = written {
        eprintln!(
            "cannot write the output of {}: {e}",
            program.to_string_lossy()
        );
        return ExitCode::FAILURE;
    }
    let status = output
        .status
        .code()
        .unwrap_or_else(|| 128 + output.status.signal().unwrap_or(0));
    let Ok(usage) = getrusage(UsageWho::RUSAGE_CHILDREN) else {
        eprintln!("cannot read the resource usage");
        return ExitCode::FAILURE;
    };
    // macOS counts bytes, and Linux kilobytes.
    let unit = if cfg!(target_os = "macos") { 1 } else { 1024 };
    let peak = u64::try_from(usage.max_rss()).unwrap_or(0) * unit;
    let count = |n: Option<u64>| n.map_or_else(|| "-".to_owned(), |n| n.to_string());
    let (pi, pc) = counts
        .performance
        .map_or((None, None), |p| (Some(p.instructions), Some(p.cycles)));
    println!(
        "{status} {} {} {} {} {} {} {peak}",
        wall.as_nanos(),
        counts.cpu.as_nanos(),
        count(counts.instructions),
        count(counts.cycles),
        count(pi),
        count(pc),
    );
    ExitCode::SUCCESS
}

/// Runs `command` once by way of the helper, with `dir` for its output, and gives what the run
/// cost, what it printed on stdout and what it printed on stderr.
pub(crate) fn run(command: &[OsString], dir: &Path) -> Result<(Sample, Vec<u8>, String), String> {
    let helper = std::env::current_exe().map_err(|e| format!("cannot find the harness: {e}"))?;
    let (stdout, stderr) = (dir.join("stdout"), dir.join("stderr"));
    let output = Command::new(helper)
        .arg("sample")
        .arg("--stdout")
        .arg(&stdout)
        .arg("--stderr")
        .arg(&stderr)
        .arg("--")
        .args(command)
        .output()
        .map_err(|e| format!("cannot run the helper: {e}"))?;
    let program = command
        .first()
        .map_or_else(String::new, |p| p.to_string_lossy().into_owned());
    let line = String::from_utf8_lossy(&output.stdout);
    let sample = parse(line.trim()).ok_or_else(|| {
        format!(
            "cannot measure {program}: {}",
            String::from_utf8_lossy(&output.stderr)
        )
    })?;
    let read = |path: &Path| {
        std::fs::read(path).map_err(|e| format!("cannot read {}: {e}", path.display()))
    };
    let printed = read(&stdout)?;
    let errors = String::from_utf8_lossy(&read(&stderr)?).into_owned();
    Ok((sample, printed, errors))
}

/// The helper's line: status, wall and CPU nanoseconds, instructions, cycles, those on the
/// performance cores, and the peak, each count `-` where the system keeps none.
pub(crate) fn parse(line: &str) -> Option<Sample> {
    let fields: Vec<&str> = line.split(' ').collect();
    let [status, wall, cpu, instructions, cycles, pi, pc, peak] = fields[..] else {
        return None;
    };
    let count = |s: &str| {
        if s == "-" {
            Some(None)
        } else {
            s.parse().ok().map(Some)
        }
    };
    let nanos = |s: &str| s.parse().ok().map(Duration::from_nanos);
    let performance = match (count(pi)?, count(pc)?) {
        (Some(instructions), Some(cycles)) => Some(Performance {
            instructions,
            cycles,
        }),
        _ => None,
    };
    Some(Sample {
        counts: Counts {
            instructions: count(instructions)?,
            cycles: count(cycles)?,
            performance,
            cpu: nanos(cpu)?,
        },
        wall: nanos(wall)?,
        peak: peak.parse().ok()?,
        status: status.parse().ok()?,
    })
}

/// The timed runs of a program.
#[derive(Debug, Default)]
pub(crate) struct Runs {
    pub(crate) samples: Vec<Sample>,
}

impl Runs {
    /// The program's time: its runs' counts added together, divided by their number, or their
    /// wall times so, where that is less (Goals, Timing).
    pub(crate) fn time(&self) -> Duration {
        let total = self
            .samples
            .iter()
            .fold(Counts::ZERO, |t, s| t.plus(s.counts));
        let wall = self.samples.iter().map(|s| s.wall).sum();
        let n = u32::try_from(self.samples.len().max(1)).unwrap_or(u32::MAX);
        total.idle_time(wall) / n
    }

    /// Each run's time, in seconds.
    pub(crate) fn times(&self) -> Vec<f64> {
        self.samples
            .iter()
            .map(|s| s.time().as_secs_f64())
            .collect()
    }

    /// The standard deviation of the runs' times, over their mean.
    pub(crate) fn spread(&self) -> f64 {
        let times = self.times();
        let n = float(times.len() as u64);
        if times.len() < 2 {
            return 0.0;
        }
        let mean = times.iter().sum::<f64>() / n;
        let variance = times.iter().map(|t| (t - mean).powi(2)).sum::<f64>() / (n - 1.0);
        variance.sqrt() / mean
    }

    /// The instructions of a run, the mean of the runs', where the system counts them.
    pub(crate) fn instructions(&self) -> Option<u64> {
        let total = self
            .samples
            .iter()
            .map(|s| s.counts.instructions)
            .sum::<Option<u64>>()?;
        Some(total / (self.samples.len().max(1) as u64))
    }

    /// The least peak resident memory of the runs, in bytes.
    pub(crate) fn peak(&self) -> u64 {
        self.samples.iter().map(|s| s.peak).min().unwrap_or(0)
    }
}

/// A count as a float, for the report.
#[allow(
    clippy::cast_precision_loss,
    reason = "the counts of a run fit a double's 53 bits for 26 days of cycles"
)]
pub(crate) fn float(n: u64) -> f64 {
    n as f64
}
