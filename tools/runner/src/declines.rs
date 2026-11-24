//! The tests an implementation of part of the language may decline: those a file lists, so
//! that no test moves from passing to declined unseen (`--known-declines`).

use std::collections::HashSet;
use std::path::Path;

use crate::runner::{Outcome, Record};

/// Fails each declined test that `file` doesn't list, and names the listed tests that no longer
/// decline, which the file can drop.
pub(crate) fn fail_unknown(records: &mut [Record], file: &Path) -> Result<(), String> {
    let text = std::fs::read_to_string(file)
        .map_err(|error| format!("cannot read {}: {error}", file.display()))?;
    let known: HashSet<&str> = text
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    let mut declined = HashSet::new();
    for record in records.iter_mut() {
        if !matches!(record.outcome, Outcome::Declined) {
            continue;
        }
        declined.insert(record.name.clone());
        if !known.contains(record.name.as_str()) {
            let why = format!("declined, which {} doesn't list", file.display());
            record.outcome = Outcome::Failed(vec![why]);
        }
    }
    let mut dropped: Vec<&str> = known
        .into_iter()
        .filter(|t| !declined.contains(*t))
        .collect();
    dropped.sort_unstable();
    for test in dropped {
        println!(
            "note: {test} no longer declines, so {} can drop it",
            file.display()
        );
    }
    Ok(())
}
