//! The human rendering of a run of tests: each failure with its place, what it was and why it
//! failed, then one line that counts the results. A passing result has no line of its own. `--json`
//! has the same results as objects (conformance.test-objects), each with its kind and name, and a
//! failure with the same lines of why.

use std::fmt::Write as _;

use super::plan::{Case, Kind, Ran, Why};

/// The failures of `cases`, whose results are `results`, then the count, as lines of stdout.
/// With `errors`, no test ran, and there is no count.
pub(super) fn text(cases: &[Case], results: &[Ran], errors: bool) -> String {
    let mut out = String::new();
    for (case, ran) in cases.iter().zip(results).filter(|(_, r)| !r.passed) {
        let _ = writeln!(out, "{}:{}: {} failed", case.file, case.line, label(case));
        for line in reasons(case, ran) {
            let _ = writeln!(out, "  {line}");
        }
    }
    if !errors {
        out.push_str(&count(cases, results));
    }
    out
}

/// The panic reports of the failures, which `--json` writes to stderr, as a run writes them.
pub(super) fn reports(cases: &[Case], results: &[Ran]) -> String {
    cases
        .iter()
        .zip(results)
        .filter(|(case, _)| case.cached.is_none())
        .filter_map(|(_, r)| match &r.why {
            Some(Why::Panicked(report)) => Some(report.as_str()),
            _ => None,
        })
        .collect()
}

/// The kind of a case, as `--json` writes it.
pub(super) fn kind(case: &Case) -> &'static str {
    match case.kind {
        Kind::Test => "test",
        Kind::Example => "example",
        Kind::Property => "property",
    }
}

/// What the case is: a test by its name, a doc example or a property by its text.
fn label(case: &Case) -> String {
    match case.kind {
        Kind::Test => format!("test \"{}\"", case.name),
        Kind::Example => format!("example `{}`", case.name),
        Kind::Property => format!("property `{}`", case.name),
    }
}

/// Why a failure failed, one line each.
pub(super) fn reasons(case: &Case, ran: &Ran) -> Vec<String> {
    if let Some(verdict) = &ran.property {
        let names = case.property.as_ref().map_or(&[][..], |p| &p.names[..]);
        return verdict.lines(names);
    }
    match &ran.why {
        Some(Why::Panicked(report)) => report.lines().map(str::to_owned).collect(),
        Some(Why::Raised(shown)) => vec![format!("raised {shown}")],
        Some(Why::Compared(left, right)) => {
            vec![format!("left:  {left}"), format!("right: {right}")]
        }
        Some(Why::Exited) => vec!["called `exit`".to_owned()],
        Some(Why::False) | None => vec!["evaluated to false".to_owned()],
    }
}

/// How many results passed and failed, and how many came from earlier runs.
fn count(cases: &[Case], results: &[Ran]) -> String {
    let passed = results.iter().filter(|r| r.passed).count();
    let reused = cases.iter().filter(|c| c.cached.is_some()).count();
    let mut line = format!("{passed} passed, {} failed", results.len() - passed);
    if reused > 0 {
        let _ = write!(line, " ({reused} reused from earlier runs)");
    }
    line.push('\n');
    line
}
