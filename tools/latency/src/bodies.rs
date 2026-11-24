//! The time each body of a program takes to check, every phase included, once the program's names
//! and declarations are known, and the facts of reflection that every body shares, which read
//! every body of the program and of the standard library and which the engine computes once
//! (goal bounded-checking). Otherwise the first body in a database whose check asks for them
//! would be timed with the standard library's inference. As every time is (Goals, Timing), a body's
//! is the median of 5 runs after one warm-up run, each run in a database of its own, since a
//! database checks a body once. One run of every program finds the candidates: a run is rarely
//! faster than its median, so the slowest median is among the programs whose one run is slowest,
//! and only those are run again.

use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::clock::Clock;
use stilt_db::Database;

/// The runs measured after the warm-up.
const RUNS: usize = 5;

/// The programs whose one run is slowest, which are run again for their medians.
const CANDIDATES: usize = 10;

/// The slowest body of the programs: its median time, and where it is.
pub(crate) fn slowest(programs: &[PathBuf]) -> Result<(Duration, String), String> {
    let mut once = Vec::with_capacity(programs.len());
    for program in programs {
        let slowest = times(program)?.into_iter().map(|(_, time)| time).max();
        once.push((slowest.unwrap_or_default(), program));
    }
    once.sort_by_key(|(time, _)| std::cmp::Reverse(*time));
    let mut slowest = (Duration::ZERO, String::new());
    for (_, program) in once.into_iter().take(CANDIDATES) {
        let (time, at) = median(program)?;
        if time > slowest.0 {
            slowest = (time, format!("{}: {at}", program.display()));
        }
    }
    Ok(slowest)
}

/// The slowest body of the program at `path` by its median time, and where it is.
fn median(path: &Path) -> Result<(Duration, String), String> {
    let mut runs = Vec::with_capacity(RUNS);
    for run in 0..=RUNS {
        let times = times(path)?;
        if run > 0 {
            runs.push(times);
        }
    }
    let mut slowest = (Duration::ZERO, String::new());
    for (body, (at, _)) in runs[0].iter().enumerate() {
        let mut times: Vec<Duration> = runs.iter().map(|run| run[body].1).collect();
        times.sort();
        let median = times[RUNS / 2];
        if median > slowest.0 {
            slowest = (median, at.clone());
        }
    }
    Ok(slowest)
}

/// The time each body of the program at `path` takes to check, in a fresh database, in the
/// order of its files and their bodies.
fn times(path: &Path) -> Result<Vec<(String, Duration)>, String> {
    let db = Database::default();
    let program = stilt_db::load(&db, path)?;
    stilt_hir::check(&db, program);
    // Every reflection summary, as `reflections` reads them for whichever body asks first.
    let _ = stilt_types::reflects::tested_traits(&db, program);
    let mut times = Vec::new();
    for &file in program.files(&db) {
        let bodies = stilt_hir::resolve_module(&db, program, file).bodies.len();
        for index in 0..u32::try_from(bodies).expect("under 4G bodies") {
            let start = Clock::own();
            stilt_types::body_diagnostics(&db, program, file, index);
            times.push((format!("{}, body {index}", file.path(&db)), start.elapsed()));
        }
    }
    Ok(times)
}
