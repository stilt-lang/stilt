//! The shootout's measurements of one version: a clean check and a clean debug build, each from
//! no cache; then, warm, the time from an edit that breaks the middle module to its diagnostics,
//! and from the edit that fixes it again to a clean check; and the time from an edit to the
//! running program printing what the edit changed. Times are the wall time of the commands, as
//! a programmer waits for them.

use std::io::{BufRead, BufReader};
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use super::Language;
use super::project::{self, Edit, Shape};
use super::tools::{Step, Tools};

/// How long a running program may take to print a line.
const PATIENCE: Duration = Duration::from_secs(120);

/// The times of one measurement's runs.
#[derive(Debug, Default)]
pub(crate) struct Times(pub(crate) Vec<Duration>);

impl Times {
    pub(crate) fn median(&self) -> Option<Duration> {
        let mut sorted = self.0.clone();
        sorted.sort();
        sorted.get(sorted.len() / 2).copied()
    }

    pub(crate) fn range(&self) -> Option<(Duration, Duration)> {
        Some((*self.0.iter().min()?, *self.0.iter().max()?))
    }
}

/// What the shootout measured of a version.
#[derive(Debug, Default)]
pub(crate) struct Measured {
    pub(crate) lines: usize,
    pub(crate) clean_check: Times,
    pub(crate) clean_build: Times,
    pub(crate) to_error: Times,
    pub(crate) to_fixed: Times,
    pub(crate) to_running: Times,
    /// What the built program prints.
    pub(crate) printed: String,
}

/// Runs `command` and gives its wall time, failing unless it succeeds as `succeeds` says.
fn timed(command: Command, succeeds: bool) -> Result<Duration, String> {
    Ok(timed_output(command, succeeds)?.0)
}

/// As [`timed`], with what the command printed.
fn timed_output(mut command: Command, succeeds: bool) -> Result<(Duration, String), String> {
    let start = Instant::now();
    let output = command
        .output()
        .map_err(|e| format!("cannot run {}: {e}", shown(&command)))?;
    let time = start.elapsed();
    if output.status.success() != succeeds {
        return Err(format!(
            "{} {}:\n{}{}",
            shown(&command),
            if succeeds {
                "failed"
            } else {
                "succeeded, with a type error in its project"
            },
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let printed = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    Ok((time, printed))
}

/// A command as a shell would write it.
fn shown(command: &Command) -> String {
    std::iter::once(command.get_program())
        .chain(command.get_args())
        .map(|a| a.to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join(" ")
}

/// Measures the version of `language` in `dir`, which holds its project of `shape`.
pub(crate) fn version(
    tools: &Tools,
    language: Language,
    dir: &Path,
    shape: Shape,
    (runs, edits): (usize, usize),
) -> Result<Measured, String> {
    let mut m = Measured {
        lines: project::lines(dir),
        ..Measured::default()
    };
    for step in [Step::Check, Step::Build] {
        for _ in 0..runs {
            tools.clean(language, dir);
            let time = timed(tools.command(language, step, dir), true)?;
            match step {
                Step::Check => m.clean_check.0.push(time),
                Step::Build => m.clean_build.0.push(time),
            }
        }
    }
    let exe = Tools::executable(language, dir);
    let output = Command::new(&exe)
        .output()
        .map_err(|e| format!("cannot run {}: {e}", exe.display()))?;
    m.printed = String::from_utf8_lossy(&output.stdout).into_owned();
    let (_, printed) = timed_output(tools.command(language, Step::Check, dir), true)?;
    // A warning would cost the Stilt version time that the others don't spend.
    if language == Language::Stilt && !printed.trim().is_empty() {
        return Err(format!("the Stilt version isn't clean:\n{printed}"));
    }
    let edited = shape.edited();
    for n in 1..=edits {
        project::rewrite(language, dir, shape, edited, Some(Edit::Broken))?;
        m.to_error
            .0
            .push(timed(tools.command(language, Step::Check, dir), false)?);
        project::rewrite(language, dir, shape, edited, Some(Edit::Plus(n)))?;
        m.to_fixed
            .0
            .push(timed(tools.command(language, Step::Check, dir), true)?);
    }
    m.to_running = if language == Language::Stilt {
        hot(tools, dir, shape, edits)?
    } else {
        rebuilt(tools, language, dir, shape, edits)?
    };
    tools.clean(language, dir);
    project::rewrite(language, dir, shape, edited, None)?;
    Ok(m)
}

/// The lines a process prints, each with the time it arrived.
fn lines(child: &mut std::process::Child) -> Result<mpsc::Receiver<(Instant, String)>, String> {
    let out = child
        .stdout
        .take()
        .ok_or("the program's output isn't piped")?;
    let (send, lines) = mpsc::channel();
    std::thread::spawn(move || {
        for line in BufReader::new(out).lines().map_while(Result::ok) {
            if send.send((Instant::now(), line)).is_err() {
                break;
            }
        }
    });
    Ok(lines)
}

/// The first line from `lines` that isn't `old`, and when it arrived.
fn changed(
    lines: &mpsc::Receiver<(Instant, String)>,
    old: &str,
) -> Result<(Instant, String), String> {
    let deadline = Instant::now() + PATIENCE;
    loop {
        let left = deadline.saturating_duration_since(Instant::now());
        match lines.recv_timeout(left) {
            Ok((at, line)) if line != old => return Ok((at, line)),
            Ok(_) => {}
            Err(_) => return Err("the running program printed nothing new".to_owned()),
        }
    }
}

/// From each edit to the line that `stilt run`, which patches each edit into the running
/// program, prints with the edit's change.
fn hot(tools: &Tools, dir: &Path, shape: Shape, edits: usize) -> Result<Times, String> {
    let mut child = tools
        .hot_run(dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| format!("cannot run stilt run: {e}"))?;
    let lines = lines(&mut child)?;
    let mut times = Times::default();
    let result = (|| {
        let (_, mut last) = changed(&lines, "")?;
        for n in 1..=edits {
            let start = Instant::now();
            project::rewrite(
                Language::Stilt,
                dir,
                shape,
                shape.edited(),
                Some(Edit::Plus(100 + n)),
            )?;
            let (at, line) = changed(&lines, &last)?;
            times.0.push(at.duration_since(start));
            last = line;
        }
        Ok(())
    })();
    let _ = child.kill();
    let _ = child.wait();
    result.map(|()| times)
}

/// From each edit through a debug build and the start of the program to its first line.
fn rebuilt(
    tools: &Tools,
    language: Language,
    dir: &Path,
    shape: Shape,
    edits: usize,
) -> Result<Times, String> {
    let mut times = Times::default();
    for n in 1..=edits {
        let start = Instant::now();
        project::rewrite(
            language,
            dir,
            shape,
            shape.edited(),
            Some(Edit::Plus(100 + n)),
        )?;
        timed(tools.command(language, Step::Build, dir), true)?;
        let mut child = Command::new(Tools::executable(language, dir))
            .arg("watch")
            .stdout(Stdio::piped())
            .spawn()
            .map_err(|e| format!("cannot run the {} program: {e}", language.name()))?;
        let lines = lines(&mut child)?;
        let first = changed(&lines, "");
        let _ = child.kill();
        let _ = child.wait();
        times.0.push(first?.0.duration_since(start));
    }
    Ok(times)
}
