//! The memory of an engine that holds a project (goal bounded-cache): after a clean debug build of
//! the project, answered by the engine, and after each replay of the edit script, each edit written
//! to the project's file and checked by the engine, and the replay ended by a build. The project
//! ends as it began, each edit followed by its undoing.
//!
//! The engine's cache is the memory its allocator holds for it in use, once it is done with a
//! command: on macOS, the bytes allocated in its malloc zones, as `vmmap` reports them. Beside
//! it is what the system charges the process, its physical footprint, which also counts the
//! pages the allocator holds free between the objects in use. On Linux, both are the process's
//! resident set, which overstates the cache.

use std::fs;
use std::path::Path;
use std::process::Command;

use crate::engine::Engine;
use crate::replay::Project;
use crate::script::Edit;

/// The budget of the cache (goal bounded-cache).
const BOUNDED_CACHE: u64 = 500_000_000;

/// The budget of the engine's footprint, what the system charges the process (goal
/// bounded-cache).
const BOUNDED_FOOTPRINT: u64 = 1_000_000_000;

/// How much the cache may differ from one replay to another, every replay making the same
/// edits: what the allocator rounds, and no more.
const NOISE: u64 = 4_000_000;

/// Far less than an engine holds once it has built the 100K-line project: an engine that
/// holds less answered no build.
const BUILT: u64 = 64 << 20;

/// An engine's memory at one time, in bytes.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Memory {
    /// What its allocator holds in use: the cache.
    pub(crate) in_use: u64,
    /// What the system charges its process.
    pub(crate) footprint: u64,
    /// Whether `in_use` is what the allocator holds in use, as on macOS, rather than the
    /// resident set, which on Linux stands for it and overstates it.
    pub(crate) heap: bool,
}

/// The engine's memory, once it is done with the last command.
fn memory(engine: &Engine) -> Result<Memory, String> {
    if !engine.listens() {
        return Err("the engine stopped".to_owned());
    }
    let pid = engine.pid().to_string();
    if let Ok(status) = fs::read_to_string(format!("/proc/{pid}/status")) {
        let resident = number_after(&status, "VmRSS:").map(|kb| kb * 1024)?;
        return Ok(Memory {
            in_use: resident,
            footprint: resident,
            heap: false,
        });
    }
    let zones = output("vmmap", &["--summary", &pid])?;
    let footprint = output("footprint", &["-f", "bytes", "--noCategories", &pid])?;
    Ok(Memory {
        in_use: allocated(&zones)?,
        footprint: number_after(&footprint, "phys_footprint:")?,
        heap: true,
    })
}

fn output(program: &str, args: &[&str]) -> Result<String, String> {
    let output = Command::new(program)
        .args(args)
        .output()
        .map_err(|e| format!("cannot run {program}: {e}"))?;
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

/// The number after `name` on its line of `text`.
fn number_after(text: &str, name: &str) -> Result<u64, String> {
    text.lines()
        .find_map(|line| line.trim().strip_prefix(name))
        .and_then(|rest| rest.split_whitespace().next())
        .and_then(|n| n.parse::<u64>().ok())
        .ok_or_else(|| format!("no {name} in the measure of the engine's memory"))
}

/// The bytes allocated in all the malloc zones of `vmmap --summary`: the column of that name,
/// in the total line of the table of zones.
fn allocated(summary: &str) -> Result<u64, String> {
    summary
        .lines()
        .skip_while(|line| !line.starts_with("MALLOC ZONE"))
        .find(|line| line.starts_with("TOTAL"))
        .and_then(|line| line.split_whitespace().nth(6))
        .and_then(size)
        .ok_or_else(|| "no total of the malloc zones in vmmap's summary".to_owned())
}

/// A size as `vmmap` writes it: bytes, or a number of K, M or G of 1024 each.
fn size(text: &str) -> Option<u64> {
    let (number, unit) = match text.char_indices().last()? {
        (at, 'K') => (&text[..at], 1u64 << 10),
        (at, 'M') => (&text[..at], 1 << 20),
        (at, 'G') => (&text[..at], 1 << 30),
        _ => (text, 1),
    };
    let number: f64 = number.parse().ok()?;
    // A size in bytes is far below 2^53, so the float holds it exactly enough.
    #[allow(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        clippy::cast_precision_loss
    )]
    Some((number * unit as f64) as u64)
}

/// What the engine held after the clean build, and after each replay.
pub(crate) struct Held {
    pub(crate) built: Memory,
    pub(crate) replays: Vec<Memory>,
}

/// Builds `project` by way of an engine, then replays `edits` on it `replays` times, and
/// measures the engine's memory after the build and after each replay.
pub(crate) fn measure(
    stilt: &Path,
    project: &Path,
    loaded: &Project,
    edits: &[Edit],
    replays: usize,
) -> Result<Held, String> {
    let engine = Engine::start(stilt, project)?;
    let output = project.with_extension("engine.exe");
    let output = output.to_string_lossy();
    engine.ask(&["build", "-o", &output])?;
    let built = memory(&engine)?;
    if built.in_use < BUILT {
        return Err(format!(
            "the engine holds {} MB after the build, so it didn't answer it",
            built.in_use / 1_000_000
        ));
    }
    let mut held = Vec::new();
    for _ in 0..replays {
        for edit in edits {
            let path = project.join(&loaded.paths[edit.file]);
            fs::write(&path, &edit.text).map_err(|e| format!("{}: {e}", path.display()))?;
            engine.ask(&["check"])?;
        }
        engine.ask(&["build", "-o", &output])?;
        held.push(memory(&engine)?);
    }
    Ok(Held {
        built,
        replays: held,
    })
}

/// Prints what the engine held, and returns the targets it misses: a cache of 500 MB or more, a
/// footprint of 1 GB or more, or a cache that grows from the first replay to the last. The
/// cache's two targets are judged only where it is the allocator's heap: a resident set also
/// counts the pages the allocator keeps free, and moves with them.
pub(crate) fn report(held: &Held) -> Vec<String> {
    let mb = |bytes: u64| bytes / 1_000_000;
    let line = |memory: &Memory, after: &str| {
        println!(
            "the engine's cache is {} MB after {after}, its footprint {} MB",
            mb(memory.in_use),
            mb(memory.footprint)
        );
    };
    line(&held.built, "a clean build");
    for (i, memory) in held.replays.iter().enumerate() {
        line(memory, &format!("replay {}", i + 1));
    }
    let mut missed = Vec::new();
    if !held.built.heap {
        println!(
            "the cache is the resident set here, which overstates it: only the footprint is judged"
        );
    }
    let most = held
        .replays
        .iter()
        .chain([&held.built])
        .map(|m| m.in_use)
        .max();
    if let Some(most) = most.filter(|&most| held.built.heap && most >= BOUNDED_CACHE) {
        missed.push(format!(
            "bounded-cache: the engine's cache is {} MB",
            mb(most)
        ));
    }
    let footprint = (held.replays.iter().chain([&held.built]))
        .map(|m| m.footprint)
        .max();
    if let Some(most) = footprint.filter(|&most| most >= BOUNDED_FOOTPRINT) {
        missed.push(format!(
            "bounded-cache: the engine's footprint is {} MB",
            mb(most)
        ));
    }
    if let (Some(first), Some(last)) = (held.replays.first(), held.replays.last())
        && first.heap
        && last.in_use > first.in_use + NOISE
    {
        missed.push(format!(
            "bounded-cache: the engine's cache grows from {} MB after the first replay to {} MB after \
             the last",
            mb(first.in_use),
            mb(last.in_use)
        ));
    }
    missed
}
