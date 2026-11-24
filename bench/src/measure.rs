//! Building the suite's programs, and timing their runs and measuring their memory. A run's time is
//! its cycles on a performance core at the reference machine's clock, which the meter reads from
//! the processor's counts, so that other processes on the machine leave it nearly as it is (Goals,
//! Timing).

use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::time::{Duration, Instant};

use nix::sys::resource::{UsageWho, getrusage};
use stilt_meter::Counts;

/// Builds the Stilt program `source` into the executable `out`, as `stilt build` builds a debug
/// build (goal debug-speed: the same builds as clean-debug-build).
pub(crate) fn build_stilt(stilt: &Path, source: &Path, out: &Path) -> Result<(), String> {
    let mut command = Command::new(stilt);
    command.arg("build").arg("-o").arg(out).arg(source);
    finish(&mut command, source)
}

/// Builds the Stilt program `source` into the executable `out` as a release build
/// (builds.release-builds), with `home` as the cache, and gives how long the build took: from an
/// empty cache, a clean build's time (Goals, Compile speed).
pub(crate) fn build_release(
    stilt: &Path,
    source: &Path,
    out: &Path,
    home: &Path,
) -> Result<Duration, String> {
    let mut command = Command::new(stilt);
    command
        .args(["build", "--release", "-o"])
        .arg(out)
        .arg(source)
        .env("STILT_HOME", home);
    let start = Instant::now();
    finish(&mut command, source)?;
    Ok(start.elapsed())
}

/// Copies the program `source` into `dir`, with no profile, and counts a debug run of the copy
/// with `stilt run --profile`, which writes its profile beside it (builds.profile-form). Gives the
/// copy, whose release build reads the profile.
pub(crate) fn profile(stilt: &Path, source: &Path, dir: &Path) -> Result<PathBuf, String> {
    let _ = std::fs::remove_dir_all(dir);
    std::fs::create_dir_all(dir).map_err(|e| format!("cannot write {}: {e}", dir.display()))?;
    let copy = dir.join("main.lt");
    std::fs::copy(source, &copy).map_err(|e| format!("cannot copy {}: {e}", source.display()))?;
    let mut command = Command::new(stilt);
    command
        .args(["run", "--profile"])
        .arg(&copy)
        .stdin(Stdio::null());
    finish(&mut command, source)?;
    Ok(copy)
}

/// Builds the Rust program `source` into the executable `out` under Rust's release profile.
/// Builds the twin of the program `name` in `suite`'s `compare/alloc/`, its baseline linked with
/// mimalloc, into `out`, and gives its executable; none when the program has no twin.
pub(crate) fn build_twin(suite: &Path, name: &str, out: &Path) -> Result<Option<PathBuf>, String> {
    let dir = suite.join("compare/alloc");
    if !dir.join(format!("{name}.rs")).is_file() {
        return Ok(None);
    }
    let target = std::path::absolute(out.join("alloc"))
        .map_err(|e| format!("cannot find {}: {e}", out.display()))?;
    let mut cargo = Command::new("cargo");
    cargo.args(["build", "-q", "--release", "--locked", "--bin", name]);
    cargo.arg("--manifest-path").arg(dir.join("Cargo.toml"));
    cargo.arg("--target-dir").arg(&target);
    finish(&mut cargo, &dir.join(format!("{name}.rs")))?;
    Ok(Some(target.join("release").join(name)))
}

pub(crate) fn build_rust(rustc: &Path, source: &Path, out: &Path) -> Result<(), String> {
    let mut command = Command::new(rustc);
    command
        .args(["--edition", "2024", "-C", "opt-level=3", "-o"])
        .arg(out)
        .arg(source);
    finish(&mut command, source)
}

fn finish(command: &mut Command, source: &Path) -> Result<(), String> {
    let output = command
        .output()
        .map_err(|e| format!("cannot build {}: {e}", source.display()))?;
    if output.status.success() {
        Ok(())
    } else {
        Err(format!(
            "cannot build {}:\n{}{}",
            source.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ))
    }
}

/// Runs `exe` with the arguments `args`, and returns what its run cost, counted by the processor
/// ([`stilt_meter::Counts`]), and what it printed. A run that fails is an error.
pub(crate) fn run(exe: &Path, args: &[String]) -> Result<(Counts, Vec<u8>), String> {
    let (output, counts) = stilt_meter::run(Command::new(exe).args(args))
        .map_err(|e| format!("cannot run {}: {e}", exe.display()))?;
    if output.status.success() {
        Ok((counts, output.stdout))
    } else {
        Err(format!(
            "{} failed with {}:\n{}",
            exe.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ))
    }
}

/// The boxes a run of `exe` makes: the heap objects that hold the words of a value of a type that
/// isn't recursive, which the runtime counts and reports at the end of a run when `STILT_COUNTS`
/// is set (goal inline-values).
pub(crate) fn boxes(exe: &Path) -> Result<u64, String> {
    let output = Command::new(exe)
        .stdin(Stdio::null())
        .env("STILT_COUNTS", "1")
        .output()
        .map_err(|e| format!("cannot run {}: {e}", exe.display()))?;
    let stderr = String::from_utf8_lossy(&output.stderr);
    stderr
        .lines()
        .find_map(|l| l.strip_prefix("stilt: boxes "))
        .and_then(|n| n.trim().parse().ok())
        .ok_or_else(|| format!("{} reported no count of boxes:\n{stderr}", exe.display()))
}

/// The time of an executable's runs: their mean, and their spread, the difference between the
/// slowest and the fastest over the mean.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Timed {
    pub(crate) time: Duration,
    pub(crate) spread: f64,
    /// The instructions a run retires, on average, where the system counts them.
    pub(crate) instructions: Option<u64>,
}

/// The output of each executable, run with `args`, and the time of a run of it on the reference
/// machine, from `runs` timed runs. Each runs once first, untimed, since a system may check a new
/// executable on its first run, and the timed runs take turns, so that a change in the machine's
/// load touches each alike. Every program of the suite runs on one thread, so its cycles are its
/// time.
///
/// The time is that of the runs' counts added together, divided by their number. A run that the
/// system moved between the kinds of cores is counted from its share on the performance cores
/// ([`Counts::performance_cycles`]), and a program's phases differ in their cycles for each
/// instruction, so one run's share may flatter it or not; the shares of all its runs together fall
/// on all its phases alike (Goals, Timing).
pub(crate) fn timed(
    exes: &[&Path],
    args: &[String],
    runs: usize,
) -> Result<(Vec<Timed>, Vec<Vec<u8>>), String> {
    let mut outputs = Vec::new();
    for exe in exes {
        outputs.push(run(exe, args)?.1);
    }
    let runs = runs.max(1);
    let mut totals = vec![Counts::ZERO; exes.len()];
    let mut each = vec![Vec::new(); exes.len()];
    for _ in 0..runs {
        for ((exe, total), times) in exes.iter().zip(&mut totals).zip(&mut each) {
            let counts = run(exe, args)?.0;
            times.push(counts.time().as_secs_f64());
            *total = total.plus(counts);
        }
    }
    let n = u32::try_from(runs).map_err(|_| format!("too many runs: {runs}"))?;
    let timed = totals.into_iter().zip(each).map(|(total, times)| {
        let time = total.time() / n;
        let instructions = total.instructions.map(|i| i / u64::from(n));
        let (least, most) = times
            .iter()
            .fold((f64::MAX, 0.0f64), |(l, m), &t| (l.min(t), m.max(t)));
        let spread = if time.is_zero() {
            0.0
        } else {
            (most - least) / time.as_secs_f64()
        };
        Timed {
            time,
            spread,
            instructions,
        }
    });
    Ok((timed.collect(), outputs))
}

/// The peak resident memory of a run of `exe` with `args`, in bytes. A helper measures it, this harness
/// run as `stilt-bench peak EXE`, since the system reports only the largest peak of all the
/// processes a process has waited for.
pub(crate) fn peak(exe: &Path, args: &[String]) -> Result<u64, String> {
    let helper = std::env::current_exe().map_err(|e| format!("cannot find the harness: {e}"))?;
    let output = Command::new(helper)
        .arg("peak")
        .arg(exe)
        .args(args)
        .output()
        .map_err(|e| format!("cannot measure {}: {e}", exe.display()))?;
    let text = String::from_utf8_lossy(&output.stdout);
    text.trim().parse().map_err(|_| {
        format!(
            "cannot measure {}: {}",
            exe.display(),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

/// The helper of [`peak`]: runs `exe` with `args` and prints the peak resident memory of its run,
/// in bytes.
pub(crate) fn print_peak(exe: &Path, args: &[String]) -> ExitCode {
    if let Err(message) = run(exe, args) {
        eprintln!("{message}");
        return ExitCode::FAILURE;
    }
    match getrusage(UsageWho::RUSAGE_CHILDREN) {
        Ok(usage) => {
            // macOS counts bytes, and Linux kilobytes.
            let unit = if cfg!(target_os = "macos") { 1 } else { 1024 };
            println!("{}", u64::try_from(usage.max_rss()).unwrap_or(0) * unit);
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("cannot read the resource usage: {e}");
            ExitCode::FAILURE
        }
    }
}
