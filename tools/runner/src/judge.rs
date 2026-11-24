//! Comparing what an implementation did with what a test expects (conformance.exact-matching and
//! conformance.kinds-of-test).
//!
//! Each function returns the reasons the test fails. An empty list means it passes.

use std::cmp::Ordering;

use crate::annotations::RunSpec;
use crate::process::{Output, Status};
use crate::protocol::{Diagnostic, Placed, TestResult};

/// Matches diagnostics as an exact multiset: order doesn't matter, but duplicates do.
pub(crate) fn diagnostics(expected: &[Diagnostic], actual: &[Diagnostic]) -> Vec<String> {
    let (missing, unexpected) = difference(expected, actual);
    let missing = missing.iter().map(|d| format!("missing {d}"));
    let unexpected = unexpected.iter().map(|d| format!("unexpected {d}"));
    missing.chain(unexpected).collect()
}

/// Matches the results of tests and doc examples against the `PASS` and `FAIL` entries.
pub(crate) fn tests(expected: &[TestResult], actual: &[TestResult]) -> Vec<String> {
    let (missing, mut unexpected) = difference(expected, actual);
    let mut reasons = Vec::new();
    for want in missing {
        let same_line = unexpected
            .iter()
            .position(|got| got.file == want.file && got.line == want.line);
        match same_line {
            Some(index) => {
                let got = unexpected.remove(index);
                let (did, entry) = if got.passed {
                    ("passed", "FAIL")
                } else {
                    ("failed", "PASS")
                };
                reasons.push(format!(
                    "the test at {}:{} {did}, but is marked {entry}",
                    got.file, got.line
                ));
            }
            None => reasons.push(format!(
                "no result for the test at {}:{}",
                want.file, want.line
            )),
        }
    }
    for got in unexpected {
        reasons.push(format!(
            "an unexpected test result at {}:{}",
            got.file, got.line
        ));
    }
    reasons
}

/// The exit status of an abort (program.exit-statuses). An abort may lose buffered output, so
/// stdout isn't compared when a test expects it.
const ABORT_STATUS: i32 = 134;

/// Compares a finished run with the run keys of the test.
pub(crate) fn run(spec: &RunSpec, output: &Output) -> Vec<String> {
    let mut reasons = Vec::new();
    match output.status {
        Status::Exited(code) if code == spec.exit => {}
        Status::Exited(code) => reasons.push(format!("exit status {code}, expected {}", spec.exit)),
        status => return vec![format!("the program was {status}")],
    }
    if spec.exit != ABORT_STATUS && output.stdout != spec.stdout.as_bytes() {
        reasons.push("stdout differs from the expected output".to_owned());
    }
    if let Some(stderr) = &spec.stderr
        && output.stderr != stderr.as_bytes()
    {
        reasons.push("stderr differs from the expected output".to_owned());
    }
    if let Some(kind) = &spec.panic {
        let (report, location) = panic_report(&output.stderr);
        if !report.starts_with(&format!("panic: {kind}: ")) {
            reasons.push(format!("stderr doesn't end with a `{kind}` panic report"));
        } else if let Some(at) = &spec.panic_at
            && location != format!("  at {at}")
        {
            reasons.push(format!("the panic isn't reported at {at}"));
        }
    }
    reasons
}

/// Compares a run with the same program's run under another implementation. Both must finish
/// with the same status and print the same output, except that an abort may lose buffered
/// output, or both must run past the time limit, as a program whose edit made a loop that never
/// ends does: what each printed by then depends on its speed.
pub(crate) fn same_run(output: &Output, other: &Output) -> Vec<String> {
    if both_timed_out(output, other) {
        return Vec::new();
    }
    let (Status::Exited(code), Status::Exited(other_code)) = (output.status, other.status) else {
        return vec![format!(
            "the program {} here, and {} under the other implementation",
            output.status, other.status
        )];
    };
    let mut reasons = Vec::new();
    if code != other_code {
        reasons.push(format!(
            "exit status {code}, and {other_code} under the other implementation"
        ));
    }
    let aborted = code == ABORT_STATUS || other_code == ABORT_STATUS;
    if !aborted && output.stdout != other.stdout {
        reasons.push("stdout differs from the other implementation's".to_owned());
    }
    if !aborted && without_details(&output.stderr) != without_details(&other.stderr) {
        reasons.push("stderr differs from the other implementation's".to_owned());
    }
    reasons
}

/// `stderr` with the detail of each panic report left out where its wording is up to the
/// implementation: every kind's but `explicit`'s and `unwrap`'s, whose message `panic` and
/// `expect` give (program.panic-detail).
fn without_details(stderr: &[u8]) -> String {
    let text = String::from_utf8_lossy(stderr);
    let line = |l: &str| match l.strip_prefix("panic: ").and_then(|r| r.split_once(": ")) {
        Some((kind, _)) if kind != "explicit" && kind != "unwrap" => format!("panic: {kind}:"),
        _ => l.to_owned(),
    };
    text.split('\n').map(line).collect::<Vec<_>>().join("\n")
}

/// Why two runs that both aborted fail, when the test doesn't expect an abort: an abort, such as
/// a stack overflow or running out of memory, may lose output, so the runs' output isn't
/// compared, and an abort that nothing expects hides whatever the two runs would differ in.
pub(crate) fn unexpected_abort(spec: &RunSpec, output: &Output, other: &Output) -> Option<String> {
    let aborted = |o: &Output| o.status == Status::Exited(ABORT_STATUS);
    (spec.exit != ABORT_STATUS && aborted(output) && aborted(other)).then(|| {
        format!("the program aborted with status {ABORT_STATUS} under both implementations, which the test doesn't expect")
    })
}

/// Whether both runs went on past the time limit.
fn both_timed_out(output: &Output, other: &Output) -> bool {
    matches!(
        (output.status, other.status),
        (Status::TimedOut(_), Status::TimedOut(_))
    )
}

/// Compares a run with the same program's run under another implementation, when the program
/// may have errors, whose diagnostics each implementation writes to stderr in its own form
/// (program.programs-with-errors). Both must finish with the same status and print the same output,
/// and a panic that ends one must end the other, with the same kind and place, or both must run
/// past the time limit, as [`same_run`] says.
pub(crate) fn alike_run(output: &Output, other: &Output) -> Vec<String> {
    if both_timed_out(output, other) {
        return Vec::new();
    }
    let (Status::Exited(code), Status::Exited(other_code)) = (output.status, other.status) else {
        return vec![format!(
            "the program {} here, and {} under the other implementation",
            output.status, other.status
        )];
    };
    let mut reasons = Vec::new();
    if code != other_code {
        reasons.push(format!(
            "exit status {code}, and {other_code} under the other implementation"
        ));
    }
    let aborted = code == ABORT_STATUS || other_code == ABORT_STATUS;
    if !aborted && output.stdout != other.stdout {
        reasons.push("stdout differs from the other implementation's".to_owned());
    }
    let (here, there) = (panic_place(&output.stderr), panic_place(&other.stderr));
    if here != there {
        reasons.push(format!(
            "{}, and {} under the other implementation",
            describe_panic(here.as_ref()),
            describe_panic(there.as_ref())
        ));
    }
    reasons
}

/// The kind and the location of the panic report that ends `stderr`, if one does.
fn panic_place(stderr: &[u8]) -> Option<(String, String)> {
    let (report, location) = panic_report(stderr);
    let kind = report
        .strip_prefix("panic: ")?
        .split(": ")
        .next()?
        .to_owned();
    let at = location.strip_prefix("  at ")?.to_owned();
    Some((kind, at))
}

fn describe_panic(place: Option<&(String, String)>) -> String {
    match place {
        Some((kind, at)) => format!("a `{kind}` panic at {at}"),
        None => "no panic".to_owned(),
    }
}

/// Compares the syntax trees that `parse --sexp` printed with the same program's under another
/// implementation. Both must finish with the same status and print the same trees, and report
/// the same syntax errors: the same file, line, column and code, whatever their messages.
pub(crate) fn same_parse(output: &Output, other: &Output) -> Vec<String> {
    let (Status::Exited(code), Status::Exited(other_code)) = (output.status, other.status) else {
        return vec![format!(
            "`parse` {} here, and {} under the other implementation",
            output.status, other.status
        )];
    };
    let mut reasons = Vec::new();
    if code != other_code {
        reasons.push(format!(
            "exit status {code}, and {other_code} under the other implementation"
        ));
    }
    if output.stdout != other.stdout {
        reasons.push("the trees differ from the other implementation's".to_owned());
    }
    let (here, there) = (syntax_errors(&output.stderr), syntax_errors(&other.stderr));
    if here != there {
        reasons.push(format!(
            "syntax errors {}, and {} under the other implementation",
            here.join(", "),
            there.join(", ")
        ));
    }
    reasons
}

/// Compares the diagnostics that `check` reported with the same program's under another
/// implementation, as an exact multiset of codes at lines and columns of files.
pub(crate) fn same_check(here: &[Placed], there: &[Placed]) -> Vec<String> {
    let (ours, theirs) = difference(here, there);
    let ours = ours
        .iter()
        .map(|d| format!("{d}, not under the other implementation"));
    let theirs = theirs
        .iter()
        .map(|d| format!("{d} only under the other implementation"));
    ours.chain(theirs).collect()
}

/// The place and code of each syntax error that `parse` reports on `stderr`, as lines of the
/// form `FILE:LINE:COL: CODE: MESSAGE`.
fn syntax_errors(stderr: &[u8]) -> Vec<String> {
    String::from_utf8_lossy(stderr)
        .lines()
        .map(|line| line.splitn(3, ": ").take(2).collect::<Vec<_>>().join(": "))
        .collect()
}

/// The last two lines of `stderr`, which a panic report makes up (program.panic-report).
fn panic_report(stderr: &[u8]) -> (String, String) {
    let text = String::from_utf8_lossy(stderr);
    let mut lines = text.strip_suffix('\n').unwrap_or(&text).rsplit('\n');
    let location = lines.next().unwrap_or_default().to_owned();
    (lines.next().unwrap_or_default().to_owned(), location)
}

/// Returns the elements only in `left` and those only in `right`, counting duplicates.
fn difference<T: Clone + Ord>(left: &[T], right: &[T]) -> (Vec<T>, Vec<T>) {
    let (mut left, mut right) = (left.to_vec(), right.to_vec());
    left.sort();
    right.sort();
    let (mut only_left, mut only_right) = (Vec::new(), Vec::new());
    let (mut i, mut j) = (0, 0);
    while i < left.len() && j < right.len() {
        match left[i].cmp(&right[j]) {
            Ordering::Less => {
                only_left.push(left[i].clone());
                i += 1;
            }
            Ordering::Greater => {
                only_right.push(right[j].clone());
                j += 1;
            }
            Ordering::Equal => {
                i += 1;
                j += 1;
            }
        }
    }
    only_left.extend_from_slice(&left[i..]);
    only_right.extend_from_slice(&right[j..]);
    (only_left, only_right)
}

/// Why a run that two implementations agree on fails when it must succeed: it exited with
/// another status than 0, as when both ran out of memory (program.exit-statuses).
pub(crate) fn unsuccessful(output: &Output) -> Option<String> {
    (output.status != Status::Exited(0)).then(|| {
        format!(
            "the program {} under both implementations, and must exit with status 0",
            output.status
        )
    })
}

#[cfg(test)]
mod tests;
