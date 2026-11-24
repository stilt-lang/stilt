//! `stilt-latency`, the latency harness (Goals, Compile speed).
//!
//! `edits` replays an edit script against a warm query database and reports, for each kind of edit,
//! the time from the file's change to the program's diagnostics, and how many bodies were type
//! checked again. With `--compare`, it also checks each step against a clean check
//! (incremental-equals-clean). It fails when an edit misses a target: edit-to-diagnostics, under
//! 100 ms at the 95th percentile for body and signature edits; no-slow-edit, every edit under 1 s;
//! body-edits-recheck-one-body, a body edit type checks only its body; and
//! incremental-equals-clean, incremental diagnostics equal clean ones. The script's six kinds of
//! edit take turns, so its 300 pairs by default give each kind 100 edits, and each percentile is
//! printed with the number of edits it is drawn from.
//!
//! `bodies` times every body of each program it is given, and fails when one takes 10 ms or more to
//! check (bounded-checking).
//!
//! `hot` replays the edit script against the project held in an image, as `stilt run` holds it,
//! and fails when the time from an edit until its new code is live is 1 s or more at the 95th
//! percentile (edit-to-running-program), or when after an edit the image holds other code for a
//! function the program reaches than walking and counting the program afresh gives it
//! (incremental-equals-clean).
//!
//! `memory` builds a project by way of the compiler's engine, replays the edit script on it ten
//! times, and fails when the engine holds 1 GB or more after the build or after a replay, or holds
//! more after the last replay than after the first (bounded-cache).
//!
//! `lsp` replays the edit script through the language server, as an editor sends it, and fails when
//! the time from a buffer's change to its diagnostics is 100 ms or more at the 95th percentile for
//! body and signature edits (edit-to-diagnostics, one-engine).
//!
//! `repl` types inputs into a session of the REPL on a project, `let`s of its `main`, and fails
//! when the time from an input to its answer is 100 ms or more at the 95th percentile
//! (interactive-evaluation).
//!
//! `compile-time` replays the edit script of the compile-time benchmark on the benchmark and on its
//! baseline, each held by an engine, times each edit until the debug executable is built again, and
//! fails when the benchmark takes more than 1.2 times its baseline's time
//! (compile-time-code-rebuilds). It reports the lines of the benchmark's functions as written and
//! with each macro use expanded, and whether those are at most twice these, which it doesn't fail
//! on, the target being proposed (visible-expansion-size).

mod bodies;
mod clock;
mod editor;
mod engine;
mod hot;
mod memory;
mod rebuild;
mod repl;
mod replay;
mod running;
mod script;
mod split;

use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;

use clap::{Parser, Subcommand};

use replay::{Project, Step, clean, replay};
use script::{Kind, script};

/// Times the compiler's checks after edits, and of each body.
#[derive(Debug, Parser)]
struct Args {
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Replay an edit script on a project and time each edit.
    Edits {
        /// The project: a directory holding a program's main.lt, or a package.
        project: PathBuf,
        /// How many edits to make, each followed by its undoing: 100 of each kind by default.
        #[arg(long, default_value_t = PAIRS)]
        edits: usize,
        /// The seed that picks the edits.
        #[arg(long, default_value_t = 1)]
        seed: u64,
        /// Check each step against a clean check of the same files (incremental-equals-clean).
        #[arg(long)]
        compare: bool,
    },
    /// Replay an edit script on a project held in an image, and time each patch.
    Hot {
        /// The project: a directory holding a program's main.lt, or a package.
        project: PathBuf,
        /// How many edits to make, each followed by its undoing: 100 of each kind by default.
        #[arg(long, default_value_t = PAIRS)]
        edits: usize,
        /// The seed that picks the edits.
        #[arg(long, default_value_t = 1)]
        seed: u64,
    },
    /// Build a project by way of the compiler's engine, replay the edit script on it, and
    /// measure the engine's memory.
    Memory {
        /// The project: a directory holding a program's main.lt, or a package.
        project: PathBuf,
        /// The compiler, whose engine holds the project.
        #[arg(long)]
        stilt: PathBuf,
        /// How many times to replay the edit script.
        #[arg(long, default_value_t = 10)]
        replays: usize,
        /// How many edits to make, each followed by its undoing.
        #[arg(long, default_value_t = 24)]
        edits: usize,
        /// The seed that picks the edits.
        #[arg(long, default_value_t = 1)]
        seed: u64,
    },
    /// Replay an edit script on a project through the language server, and time each edit
    /// from the buffer's change to its diagnostics.
    Lsp {
        /// The project: a directory holding a program's main.lt, or a package.
        project: PathBuf,
        /// The compiler, whose language server and engine answer.
        #[arg(long)]
        stilt: PathBuf,
        /// How many edits to make, each followed by its undoing: 100 of each kind by default.
        #[arg(long, default_value_t = PAIRS)]
        edits: usize,
        /// The seed that picks the edits.
        #[arg(long, default_value_t = 1)]
        seed: u64,
    },
    /// Type inputs into a session of the REPL on a project, and time each from its line to its
    /// answer.
    Repl {
        /// The project: a directory holding a program's main.lt, or a package.
        project: PathBuf,
        /// The compiler, whose `run` holds the session.
        #[arg(long)]
        stilt: PathBuf,
        /// How many inputs to time.
        #[arg(long, default_value_t = 40)]
        inputs: usize,
    },
    /// Replay the edit script of the compile-time benchmark on the benchmark and its baseline, and
    /// time each edit until the debug executable is built again.
    CompileTime {
        /// The benchmark's directory, which holds `meta/`, `baseline/` and `edits.txt`.
        bench: PathBuf,
        /// The compiler, whose engines hold the versions and build them.
        #[arg(long)]
        stilt: PathBuf,
        /// Where to copy the versions, which the replay edits, and write their executables.
        #[arg(long)]
        out: PathBuf,
        /// Replay the script on this version alone, `meta` or `baseline`, which measures no target.
        #[arg(long)]
        only: Option<String>,
    },
    /// Time each body of the programs, and report the slowest.
    Bodies {
        /// Source files, or directories holding programs: each directory's entries are
        /// programs.
        #[arg(required = true)]
        programs: Vec<PathBuf>,
    },
}

/// How many pairs of an edit and its undoing a replay makes by default: 100 edits of each of
/// the script's six kinds, so that a 95th percentile is drawn from enough edits to show its tail.
const PAIRS: usize = 300;
/// The 95th percentile that edit-to-diagnostics allows body and signature edits through the
/// language server, which hands the database the one buffer that changed.
const EDIT_TO_DIAGNOSTICS: Duration = Duration::from_millis(25);
/// The 95th percentile that edit-to-diagnostics allows body and signature edits replayed on the
/// files directly, where the database reads every file again to find the one that changed.
const FILES_EDIT_TO_DIAGNOSTICS: Duration = Duration::from_millis(50);
/// The 95th percentile that edit-to-diagnostics allows type edits, which check every body that
/// reads the type again.
const TYPE_EDIT_TO_DIAGNOSTICS: Duration = Duration::from_millis(100);
/// The time that no-slow-edit allows any one edit.
const NO_SLOW_EDIT: Duration = Duration::from_millis(250);
/// The time that bounded-checking allows a body's checking.
const BOUNDED_CHECKING: Duration = Duration::from_millis(10);
/// The 95th percentile that interactive-evaluation allows a REPL answer.
const INTERACTIVE_EVALUATION: Duration = Duration::from_millis(50);

fn millis(d: Duration) -> f64 {
    d.as_secs_f64() * 1000.0
}

/// The `p`th percentile of sorted times, by the nearest rank.
fn percentile(sorted: &[Duration], p: usize) -> Duration {
    let rank = (p * sorted.len()).div_ceil(100).max(1);
    sorted[rank - 1]
}

/// Prints a line per kind of edit, and the 95th percentile of the body and signature edits.
fn report(steps: &[Step]) -> Vec<String> {
    let mut kinds: Vec<Kind> = steps.iter().map(|s| s.kind).collect();
    kinds.sort();
    kinds.dedup();
    println!("kind        edits    p50 ms    p95 ms    max ms   bodies checked   diagnostics");
    for kind in kinds {
        let of: Vec<&Step> = steps.iter().filter(|s| s.kind == kind).collect();
        let mut times: Vec<Duration> = of.iter().map(|s| s.time).collect();
        times.sort();
        let bodies = of.iter().map(|s| s.inferred).max().unwrap_or(0);
        let diagnostics = of.iter().map(|s| s.diagnostics).max().unwrap_or(0);
        println!(
            "{:<10} {:>6} {:>9.1} {:>9.1} {:>9.1} {:>8} at most {:>8} at most",
            kind.name(),
            of.len(),
            millis(percentile(&times, 50)),
            millis(percentile(&times, 95)),
            millis(*times.last().expect("a kind has an edit")),
            bodies,
            diagnostics,
        );
    }
    misses(steps)
}

/// Replays the edit script through the language server, prints each kind's times, and gives the
/// targets the edits miss: edit-to-diagnostics for body and signature edits.
fn lsp(
    stilt: &std::path::Path,
    project: &std::path::Path,
    pairs: usize,
    seed: u64,
) -> Result<Vec<String>, String> {
    let replayed = editor::replay(stilt, project, pairs, seed)?;
    let mut kinds: Vec<Kind> = replayed.iter().map(|(k, _)| *k).collect();
    kinds.sort();
    kinds.dedup();
    println!("through the language server, from a buffer's change to its diagnostics:");
    println!("kind        edits    p50 ms    p95 ms    max ms");
    for kind in kinds {
        let mut times: Vec<Duration> = (replayed.iter().filter(|(k, _)| *k == kind))
            .map(|(_, t)| *t)
            .collect();
        times.sort();
        println!(
            "{:<10} {:>6} {:>9.1} {:>9.1} {:>9.1}",
            kind.name(),
            times.len(),
            millis(percentile(&times, 50)),
            millis(percentile(&times, 95)),
            millis(*times.last().expect("a kind has an edit")),
        );
    }
    Ok(edit_to_diagnostics(
        &replayed,
        " through the language server",
        EDIT_TO_DIAGNOSTICS,
    ))
}

/// A kind of edit that edit-to-diagnostics times: its name, which edits are of it, and its target.
type Target = (&'static str, fn(Kind) -> bool, Duration);

/// Prints the 95th percentile of the body edits' times, of the signature edits' and of the type
/// edits', each with the number of edits it is drawn from, and gives edit-to-diagnostics when one
/// misses its target. `how` says how the edits were timed, and `quick` is the target of body and
/// signature edits timed so.
fn edit_to_diagnostics(edits: &[(Kind, Duration)], how: &str, quick: Duration) -> Vec<String> {
    let mut missed = Vec::new();
    let kinds: [Target; 3] = [
        ("body", Kind::in_body, quick),
        ("signature", |k| k == Kind::Signature, quick),
        ("type", |k| k == Kind::Type, TYPE_EDIT_TO_DIAGNOSTICS),
    ];
    for (name, wanted, target) in kinds {
        let mut times: Vec<Duration> = (edits.iter().filter(|(k, _)| wanted(*k)))
            .map(|(_, t)| *t)
            .collect();
        times.sort();
        if times.is_empty() {
            continue;
        }
        let p95 = percentile(&times, 95);
        let said = format!(
            "{name} edits{how} take {:.1} ms at the 95th percentile of {} edits",
            millis(p95),
            times.len()
        );
        println!("{said}");
        if p95 >= target {
            missed.push(format!("edit-to-diagnostics: {said}"));
        }
    }
    missed
}

/// The targets that the steps miss.
fn misses(steps: &[Step]) -> Vec<String> {
    let edits: Vec<(Kind, Duration)> = steps.iter().map(|s| (s.kind, s.time)).collect();
    let mut found = edit_to_diagnostics(&edits, "", FILES_EDIT_TO_DIAGNOSTICS);
    for (i, s) in steps.iter().enumerate() {
        if s.time >= NO_SLOW_EDIT {
            found.push(format!(
                "no-slow-edit: edit {i} takes {:.1} ms",
                millis(s.time)
            ));
        }
        if s.kind.in_body() && s.inferred != 1 {
            let n = s.inferred;
            found.push(format!(
                "body-edits-recheck-one-body: edit {i}, a {} edit, checks {n} bodies again",
                s.kind.name()
            ));
        }
        if s.differs {
            found.push(format!(
                "incremental-equals-clean: after edit {i}, the diagnostics differ from a clean check's"
            ));
        }
    }
    found
}

/// Replays the edit script, and returns the targets it misses.
fn edits(
    project: &std::path::Path,
    pairs: usize,
    seed: u64,
    compare: bool,
) -> Result<Vec<String>, String> {
    let mut loaded = Project::load(project)?;
    let lines: usize = loaded.texts.iter().map(|t| t.lines().count()).sum();
    let (_, clean_time) = clean(&loaded);
    println!(
        "{}: {lines} lines in {} files, checked clean, in order, in {:.1} ms",
        project.display(),
        loaded.texts.len(),
        millis(clean_time)
    );
    let modules: Vec<String> = loaded.modules.iter().map(|m| m.join(".")).collect();
    let script = script(&loaded.texts, &modules, pairs, seed);
    let steps = replay(&mut loaded, &script, compare);
    let missed = report(&steps);
    let splits: Vec<_> = steps.iter().map(|s| (s.kind, s.split)).collect();
    split::report(&splits, false);
    Ok(missed)
}

/// The engine's memory after building the project and after each replay of the edit script,
/// and the targets it misses.
fn memory(
    stilt: &std::path::Path,
    project: &std::path::Path,
    replays: usize,
    pairs: usize,
    seed: u64,
) -> Result<Vec<String>, String> {
    let loaded = Project::load(project)?;
    let modules: Vec<String> = loaded.modules.iter().map(|m| m.join(".")).collect();
    let script = script(&loaded.texts, &modules, pairs, seed);
    let held = memory::measure(stilt, project, &loaded, &script, replays)?;
    Ok(memory::report(&held))
}

/// Times every body of the programs, and returns the targets they miss.
fn bodies(paths: &[PathBuf]) -> Result<Vec<String>, String> {
    let mut programs = Vec::new();
    for path in paths {
        if path.is_dir() && !path.join("main.lt").exists() && !path.join("stilt.toml").exists() {
            let entries =
                std::fs::read_dir(path).map_err(|e| format!("{}: {e}", path.display()))?;
            programs.extend(entries.filter_map(Result::ok).map(|e| e.path()));
        } else {
            programs.push(path.clone());
        }
    }
    programs.sort();
    let slowest = bodies::slowest(&programs)?;
    println!(
        "{} programs: the slowest body checks in {:.2} ms, at {}",
        programs.len(),
        millis(slowest.0),
        slowest.1
    );
    let missed = if slowest.0 >= BOUNDED_CHECKING {
        vec![format!(
            "bounded-checking: a body takes {:.2} ms to check",
            millis(slowest.0)
        )]
    } else {
        Vec::new()
    };
    Ok(missed)
}

fn main() -> ExitCode {
    let found = match Args::parse().command {
        Command::Edits {
            project,
            edits: pairs,
            seed,
            compare,
        } => edits(&project, pairs, seed, compare),
        Command::Bodies { programs } => bodies(&programs),
        Command::Hot {
            project,
            edits: pairs,
            seed,
        } => running::hot(&project, pairs, seed),
        Command::Memory {
            project,
            stilt,
            replays,
            edits: pairs,
            seed,
        } => memory(&stilt, &project, replays, pairs, seed),
        Command::Lsp {
            project,
            stilt,
            edits: pairs,
            seed,
        } => lsp(&stilt, &project, pairs, seed),
        Command::Repl {
            project,
            stilt,
            inputs,
        } => repl::measure(&stilt, &project, inputs),
        Command::CompileTime {
            bench,
            stilt,
            out,
            only,
        } => rebuild::measure(&stilt, &bench, &out, only.as_deref()),
    };
    match found {
        Ok(missed) if missed.is_empty() => ExitCode::SUCCESS,
        Ok(missed) => {
            for m in &missed {
                println!("ERROR {m}");
            }
            ExitCode::from(1)
        }
        Err(message) => {
            eprintln!("stilt-latency: {message}");
            ExitCode::from(2)
        }
    }
}
