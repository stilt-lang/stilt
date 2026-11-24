//! The rebuilds of the compile-time benchmark (goal compile-time-code-rebuilds): the benchmark,
//! heavy in compile-time code, and its baseline, which writes the same program by hand, each held
//! by an engine of the compiler, as `stilt build` is answered while a person works, and both
//! edited by the same edit script. Each edit, and then its undoing, is timed from the change of the
//! files until `stilt build` has written the debug executable again, the versions taking turns at
//! each step, so that whatever else slows the machine slows both. The target: the benchmark
//! rebuilds within 20% of its baseline's time. Once built clean, the benchmark's size as written
//! and expanded is reported too (visible-expansion-size).

mod edits;
mod expanded;

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use edits::Edit;

use crate::clock::Clock;
use crate::engine::Engine;
use crate::millis;

/// How many times its baseline's time the benchmark may take to rebuild (goal
/// compile-time-code-rebuilds).
const COMPILE_TIME_CODE_REBUILDS: f64 = 1.2;

/// The versions of the benchmark: the program heavy in compile-time code, and its baseline.
const VERSIONS: [&str; 2] = ["meta", "baseline"];

/// A version, copied out of the benchmark's directory, held by an engine.
struct Version {
    name: &'static str,
    dir: PathBuf,
    exe: PathBuf,
    engine: Engine,
}

impl Version {
    /// Copies the version from the benchmark's directory `bench` to `out`, starts an engine
    /// for it, and builds it clean, which it times.
    fn start(
        stilt: &Path,
        bench: &Path,
        out: &Path,
        name: &'static str,
    ) -> Result<(Self, Duration), String> {
        let dir = out.join(name);
        let _ = fs::remove_dir_all(&dir);
        copy(&bench.join(name), &dir)?;
        let exe = out.join(format!("{name}.exe"));
        let version = Self {
            name,
            engine: Engine::start(stilt, &dir)?,
            dir,
            exe,
        };
        let clean = version.build(&version.clock()).map_err(|errors| {
            format!(
                "{} can't build {}, so compile-time-code-rebuilds can't be measured:\n{errors}",
                stilt.display(),
                bench.join(name).display()
            )
        })?;
        Ok((version, clean))
    }

    /// A clock of the version's work: its engine's, and the commands' it times.
    fn clock(&self) -> Clock {
        Clock::of(&[self.engine.pid()])
    }

    /// Asks the engine to build the version, and gives the time of the work from `since` until
    /// the executable is written, the engine's and the command's own, or what the build reported
    /// when it failed. The linker, a process of its own, isn't counted, for either version.
    fn build(&self, since: &Clock) -> Result<Duration, String> {
        let exe = self.exe.to_string_lossy();
        let (output, command) = self.engine.answer_counted(&["build", "-o", &exe])?;
        let time = since.elapsed_with(command);
        if output.status.success() {
            return Ok(time);
        }
        let report = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        Err(report.lines().take(20).collect::<Vec<_>>().join("\n"))
    }

    /// Writes the texts to the version's files, and times the build that follows.
    fn rebuild(&self, texts: &[(String, String)], step: &str) -> Result<Duration, String> {
        let since = self.clock();
        for (path, text) in texts {
            let file = self.dir.join(path);
            fs::write(&file, text).map_err(|e| format!("{}: {e}", file.display()))?;
        }
        self.build(&since)
            .map_err(|errors| format!("after {step}, {} doesn't build:\n{errors}", self.name))
    }

    /// The text of one of the version's files, as it is now.
    fn read(&self, path: &str) -> Result<String, String> {
        let file = self.dir.join(path);
        fs::read_to_string(&file).map_err(|e| format!("{}: {e}", file.display()))
    }

    /// The lines and the files of the version's sources.
    fn size(&self) -> Result<(usize, usize), String> {
        let mut found = Vec::new();
        sources(&self.dir, &mut found)?;
        let mut lines = 0;
        for file in &found {
            lines += fs::read_to_string(file)
                .map_err(|e| format!("{}: {e}", file.display()))?
                .lines()
                .count();
        }
        Ok((lines, found.len()))
    }
}

/// Copies the directory `from`, and every directory and file below it, to `to`.
fn copy(from: &Path, to: &Path) -> Result<(), String> {
    fs::create_dir_all(to).map_err(|e| format!("{}: {e}", to.display()))?;
    let entries = fs::read_dir(from).map_err(|e| format!("{}: {e}", from.display()))?;
    for entry in entries.filter_map(Result::ok) {
        let (path, target) = (entry.path(), to.join(entry.file_name()));
        if path.is_dir() {
            copy(&path, &target)?;
        } else {
            fs::copy(&path, &target).map_err(|e| format!("{}: {e}", path.display()))?;
        }
    }
    Ok(())
}

/// The source files under `dir`.
fn sources(dir: &Path, found: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries = fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    for path in entries.filter_map(Result::ok).map(|e| e.path()) {
        if path.is_dir() {
            sources(&path, found)?;
        } else if path.extension().is_some_and(|e| e == "lt") {
            found.push(path);
        }
    }
    Ok(())
}

/// The times of one edit's steps: the edit and its undoing, in each version.
struct Timed {
    kind: String,
    times: Vec<Duration>,
}

/// Replays the benchmark's edit script on its versions, or on the one `only` names, and returns the
/// targets they miss: compile-time-code-rebuilds, when both are replayed.
pub(crate) fn measure(
    stilt: &Path,
    bench: &Path,
    out: &Path,
    only: Option<&str>,
) -> Result<Vec<String>, String> {
    let text = fs::read_to_string(bench.join("edits.txt"))
        .map_err(|e| format!("{}: {e}", bench.join("edits.txt").display()))?;
    let script = edits::parse(&text)?;
    let names: Vec<&'static str> = match only {
        None => VERSIONS.to_vec(),
        Some(name) => vec![VERSIONS.into_iter().find(|v| *v == name).ok_or_else(|| {
            format!("{name} is no version of the benchmark: they are meta and baseline")
        })?],
    };
    if let Some(edit) = script.iter().find(|e| !e.changes_each(&VERSIONS)) {
        return Err(format!(
            "the edit \"{}\" doesn't change both versions",
            edit.what
        ));
    }
    println!(
        "the compile-time benchmark, {}: {} edits, each followed by its undoing",
        bench.display(),
        script.len()
    );
    let mut versions = Vec::new();
    for name in names {
        let (version, clean) = Version::start(stilt, bench, out, name)?;
        let (lines, files) = version.size()?;
        println!(
            "{name}: {lines} lines in {files} files, built clean in {:.1} ms",
            millis(clean)
        );
        if name == VERSIONS[0] {
            println!("{}", expanded::report(name, expanded::measure(&version)?));
        }
        versions.push(version);
    }
    let timed = replay(&versions, &script)?;
    Ok(report(&versions, &timed))
}

/// Makes each edit of the script, then undoes it, timing each step in each version in turn.
fn replay(versions: &[Version], script: &[Edit]) -> Result<Vec<Timed>, String> {
    let mut timed = Vec::new();
    for edit in script {
        let mut steps = Vec::new();
        for v in versions {
            let edited = edit.apply(v.name, |path| v.read(path))?;
            let before = (edited.iter())
                .map(|(path, _)| Ok((path.clone(), v.read(path)?)))
                .collect::<Result<Vec<_>, String>>()?;
            steps.push((v, edited, before));
        }
        let mut spent = vec![Duration::ZERO; versions.len()];
        for (i, (v, edited, _)) in steps.iter().enumerate() {
            spent[i] += v.rebuild(edited, &format!("the edit \"{}\"", edit.what))?;
        }
        for (i, (v, _, before)) in steps.iter().enumerate() {
            spent[i] += v.rebuild(before, &format!("undoing the edit \"{}\"", edit.what))?;
        }
        timed.push(Timed {
            kind: edit.kind.clone(),
            times: spent,
        });
    }
    Ok(timed)
}

/// The durations, in milliseconds, each in a column of the report.
fn columns(durations: impl Iterator<Item = Duration>) -> String {
    durations.fold(String::new(), |mut row, d| {
        let _ = write!(row, "{:>13.1}", millis(d));
        row
    })
}

/// Prints each kind of edit's time in each version, and the totals, and returns the targets
/// they miss.
fn report(versions: &[Version], timed: &[Timed]) -> Vec<String> {
    let mut kinds: Vec<&str> = timed.iter().map(|t| t.kind.as_str()).collect();
    kinds.sort_unstable();
    kinds.dedup();
    let head = versions.iter().fold(String::new(), |mut head, v| {
        let _ = write!(head, "{:>10} ms", v.name);
        head
    });
    println!("kind        edits{head}");
    let total = |of: &[&Timed], i: usize| of.iter().map(|t| t.times[i]).sum::<Duration>();
    for kind in kinds {
        let of: Vec<&Timed> = timed.iter().filter(|t| t.kind == kind).collect();
        let row = columns((0..versions.len()).map(|i| total(&of, i)));
        println!("{kind:<10} {:>6}{row}", 2 * of.len());
    }
    let all: Vec<&Timed> = timed.iter().collect();
    let sums: Vec<Duration> = (0..versions.len()).map(|i| total(&all, i)).collect();
    let row = columns(sums.iter().copied());
    println!("{:<10} {:>6}{row}", "total", 2 * timed.len());
    let [meta, baseline] = sums[..] else {
        return Vec::new();
    };
    let ratio = meta.as_secs_f64() / baseline.as_secs_f64();
    println!("the benchmark rebuilds in {ratio:.2} times its baseline's time");
    if ratio > COMPILE_TIME_CODE_REBUILDS {
        vec![format!(
            "compile-time-code-rebuilds: the compile-time benchmark rebuilds in {ratio:.2} times its baseline's time, over {COMPILE_TIME_CODE_REBUILDS}"
        )]
    } else {
        Vec::new()
    }
}
