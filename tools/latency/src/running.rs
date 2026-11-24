//! The replay of the edit script on a project held in an image, timed until each edit's code is
//! live in the running program (goal edit-to-running-program), and checked against a fresh walk
//! (goal incremental-equals-clean).

use std::time::Duration;

use crate::replay::Project;
use crate::script::{Kind, script};
use crate::{hot, millis, percentile, split};

/// The 95th percentile that edit-to-running-program allows the edits that patch the program.
const EDIT_TO_RUNNING_PROGRAM: Duration = Duration::from_millis(250);
/// The 95th percentile that edit-to-running-program allows body edits.
const BODY_EDIT_TO_RUNNING_PROGRAM: Duration = Duration::from_millis(100);

/// Replays the edit script on the project held in an image, and returns the targets it misses.
pub(crate) fn hot(
    project: &std::path::Path,
    pairs: usize,
    seed: u64,
) -> Result<Vec<String>, String> {
    let mut loaded = Project::load(project)?;
    let lines: usize = loaded.texts.iter().map(|t| t.lines().count()).sum();
    println!(
        "{}: {lines} lines in {} files",
        project.display(),
        loaded.texts.len()
    );
    let modules: Vec<String> = loaded.modules.iter().map(|m| m.join(".")).collect();
    let script = script(&loaded.texts, &modules, pairs, seed);
    let (first, steps) = hot::replay_hot(&mut loaded, &script)?;
    println!("checked and compiled clean in {:.1} ms", millis(first));
    println!("kind        edits    p50 ms    p95 ms    max ms   compiled   restarts   with errors");
    let mut kinds: Vec<Kind> = steps.iter().map(|s| s.kind).collect();
    kinds.sort();
    kinds.dedup();
    for kind in kinds {
        let of: Vec<&hot::HotStep> = steps.iter().filter(|s| s.kind == kind).collect();
        let mut times: Vec<Duration> = of.iter().map(|s| s.time).collect();
        times.sort();
        println!(
            "{:<10} {:>6} {:>9.1} {:>9.1} {:>9.1} {:>10} {:>10} {:>13}",
            kind.name(),
            of.len(),
            millis(percentile(&times, 50)),
            millis(percentile(&times, 95)),
            millis(*times.last().expect("a kind has an edit")),
            of.iter().map(|s| s.compiled).max().unwrap_or(0),
            of.iter().filter(|s| s.restarts).count(),
            of.iter().filter(|s| s.errors).count(),
        );
    }
    let splits: Vec<_> = steps.iter().map(|s| (s.kind, s.split)).collect();
    split::report(&splits, true);
    let mut patched: Vec<Duration> = steps.iter().filter(|s| !s.errors).map(|s| s.time).collect();
    patched.sort();
    let p95 = patched.first().map(|_| percentile(&patched, 95));
    println!(
        "edits that patch the program: {}, {:.1} ms at the 95th percentile",
        patched.len(),
        p95.map_or(0.0, millis)
    );
    let mut missed = match p95 {
        Some(p95) if p95 >= EDIT_TO_RUNNING_PROGRAM => vec![format!(
            "edit-to-running-program: an edit takes {:.1} ms to reach the running program at the 95th percentile",
            millis(p95)
        )],
        _ => Vec::new(),
    };
    missed.extend(body_edits_running(&steps));
    for (i, s) in steps.iter().enumerate().filter(|(_, s)| s.differs) {
        missed.push(format!(
            "incremental-equals-clean: after edit {i}, a {} edit, the running program's code differs from a fresh walk's",
            s.kind.name()
        ));
    }
    Ok(missed)
}

/// Prints the 95th percentile of the body edits' time to reach the running program, and gives
/// edit-to-running-program when it misses its target for them.
fn body_edits_running(steps: &[hot::HotStep]) -> Option<String> {
    let mut times: Vec<Duration> = (steps.iter())
        .filter(|s| s.kind == Kind::Body && !s.errors)
        .map(|s| s.time)
        .collect();
    times.sort();
    if times.is_empty() {
        return None;
    }
    let p95 = percentile(&times, 95);
    let said = format!(
        "body edits reach the running program in {:.1} ms at the 95th percentile of {} edits",
        millis(p95),
        times.len()
    );
    println!("{said}");
    (p95 >= BODY_EDIT_TO_RUNNING_PROGRAM).then(|| format!("edit-to-running-program: {said}"))
}
