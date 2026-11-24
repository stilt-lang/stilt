//! `stilt diff OLD NEW`: the changes between the APIs of two versions of a package, and the change
//! of version number they need (versions.api and versions.change-needed), as the check of a version
//! computes them before it writes one into a manifest.

use std::fmt::Write as _;
use std::path::Path;

use stilt_pkg::api::{Apis, changes, needed};
use stilt_pkg::{Change, Version};

use crate::report::Report;

/// What `stilt diff OLD NEW [--from VERSION]` prints: each change, in the order of its address,
/// with what it needs, then the change the version needs, and with `--from`, the version that
/// follows it. A side with an error is refused with that error.
pub(crate) fn command(old: &Path, new: &Path, from: Option<&str>) -> Report {
    let from = match from.map(|v| Version::parse(v).ok_or(v)) {
        Some(Err(v)) => return Report::refuse(&format!("`{v}` is no version, as 1.4.2 is")),
        Some(Ok(v)) => Some(v),
        None => None,
    };
    let mut apis = crate::packages::Checked;
    let (before, after) = match (apis.api(old), apis.api(new)) {
        (Ok(a), Ok(b)) => (a, b),
        (Err(e), _) => return Report::refuse(&format!("{} has an error: {e}", old.display())),
        (_, Err(e)) => return Report::refuse(&format!("{} has an error: {e}", new.display())),
    };
    let steps = changes(&before, &after);
    let mut out = String::new();
    for step in &steps {
        let _ = writeln!(out, "{:<5}  {}", word(step.needs), step.described());
    }
    let need = needed(&steps);
    let _ = match from {
        Some(v) => writeln!(out, "needs {} version: {v} → {}", noun(need), v.next(need)),
        None => writeln!(out, "needs {} version", noun(need)),
    };
    Report {
        stdout: out,
        ..Report::default()
    }
}

fn word(change: Change) -> &'static str {
    match change {
        Change::Major => "major",
        Change::Minor => "minor",
        Change::Patch => "patch",
    }
}

fn noun(change: Change) -> &'static str {
    match change {
        Change::Major => "a new major",
        Change::Minor => "a new minor",
        Change::Patch => "only a new patch",
    }
}
