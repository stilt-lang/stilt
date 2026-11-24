//! Running one test: the commands each kind of test needs, in order (conformance.kinds-of-test).

use std::collections::BTreeSet;
use std::fmt::Write as _;

use crate::annotations::{Kind, RunSpec, Spec};
use crate::discovery::Test;
use crate::judge;
use crate::process::Output;
use crate::protocol::{self, Implementation, Step};

/// The outcome of one test, with what is needed to explain a failure.
#[derive(Debug)]
pub(crate) struct Record {
    pub(crate) name: String,
    pub(crate) outcome: Outcome,
    /// What the test expected, as text for the failure log.
    pub(crate) expected: String,
    /// Every command the test ran.
    pub(crate) steps: Vec<Step>,
}

#[derive(Debug)]
pub(crate) enum Outcome {
    Passed,
    Failed(Vec<String>),
    Malformed(String),
    /// The implementation declined to run the test's program.
    Declined,
}

/// The reason a run gives when the implementation declines its program.
const DECLINED: &str = "the implementation declines to run the program";

/// A test with what it expects, or the reason that can't be read.
#[derive(Debug)]
pub(crate) struct Case {
    pub(crate) test: Test,
    pub(crate) spec: Result<Spec, String>,
}

/// What a comparison of two runs requires besides runs that agree.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Also {
    /// That the program's tests have the same results under both implementations.
    pub(crate) tests: bool,
    /// That each run exits with status 0, so that two runs that fail alike don't pass.
    pub(crate) succeeds: bool,
}

/// What a test is compared with.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Against<'a> {
    /// What the test expects.
    Expected,
    /// For a run test, the program's run under another implementation, which must also report
    /// the expected diagnostics, with what else the comparison requires.
    Runs(&'a Implementation, Also),
    /// The program's syntax trees under another implementation, whatever the test expects.
    Trees(&'a Implementation),
    /// The program's diagnostics under another implementation, whatever the test expects: only
    /// those of the given codes, when they are given.
    Checks(&'a Implementation, Option<&'a BTreeSet<String>>),
    /// The program's run under another implementation, whatever the test expects and whether
    /// or not the program has errors (program.programs-with-errors).
    Alike(&'a Implementation),
}

/// Runs a test against `implementation` and judges the result.
pub(crate) fn execute(
    implementation: &Implementation,
    against: Against<'_>,
    case: &Case,
) -> Record {
    let test = &case.test;
    let compared = match against {
        Against::Trees(other) => Some(("trees", other, Compared::Trees)),
        Against::Checks(other, codes) => Some(("diagnostics", other, Compared::Checks(codes))),
        Against::Alike(other) => Some(("run", other, Compared::Runs)),
        Against::Expected | Against::Runs(..) => None,
    };
    if let Some((what, other, compared)) = compared {
        return compare(implementation, other, what, compared, case);
    }
    let spec = match &case.spec {
        Ok(spec) => spec,
        Err(reason) => {
            return Record {
                name: test.name.clone(),
                outcome: Outcome::Malformed(reason.clone()),
                expected: String::new(),
                steps: Vec::new(),
            };
        }
    };
    let mut session = Session {
        implementation,
        test,
        spec,
        steps: Vec::new(),
    };
    let reasons = match (&spec.kind, against) {
        (Kind::Run(run), Against::Runs(other, also)) => session.differential(run, other, also),
        _ => crate::erased::judged(session.judge(), &mut session),
    };
    implementation.stop_engine(test, &session.steps);
    if let Against::Runs(other, _) = against {
        other.stop_engine(test, &session.steps);
    }
    record(test, reasons, describe(spec), session.steps)
}

/// Compares what the test's program gives under two implementations, whatever it expects.
fn compare(
    implementation: &Implementation,
    other: &Implementation,
    what: &str,
    compared: Compared<'_>,
    case: &Case,
) -> Record {
    let test = &case.test;
    let mut steps = Vec::new();
    let reasons = match compared {
        Compared::Trees => trees(implementation, other, test, &mut steps),
        Compared::Checks(codes) => checks(implementation, other, codes, test, &mut steps),
        Compared::Runs => runs(implementation, other, test, given(case), &mut steps),
    };
    implementation.stop_engine(test, &steps);
    other.stop_engine(test, &steps);
    let expected = format!("the other implementation's {what}\n");
    record(test, reasons, expected, steps)
}

/// The record of a test whose commands, run as `steps`, gave `reasons` to fail.
fn record(
    test: &Test,
    reasons: Result<Vec<String>, String>,
    expected: String,
    steps: Vec<Step>,
) -> Record {
    let reasons = reasons.unwrap_or_else(|reason| vec![reason]);
    Record {
        name: test.name.clone(),
        outcome: if reasons.is_empty() {
            Outcome::Passed
        } else if reasons == [DECLINED] {
            Outcome::Declined
        } else {
            Outcome::Failed(reasons)
        },
        expected,
        steps,
    }
}

/// The commands of one test. Each method returns the reasons the test fails, or the reason
/// the implementation broke the protocol.
pub(crate) struct Session<'a> {
    pub(crate) implementation: &'a Implementation,
    pub(crate) test: &'a Test,
    pub(crate) spec: &'a Spec,
    pub(crate) steps: Vec<Step>,
}

impl Session<'_> {
    /// Runs the commands that the test's kind needs, and judges them by what it expects.
    pub(crate) fn judge(&mut self) -> Result<Vec<String>, String> {
        match &self.spec.kind {
            Kind::Check => self.check(),
            Kind::TestBlocks(_) => self.test_blocks(),
            Kind::Run(run) => self.run(run),
        }
    }

    fn check(&mut self) -> Result<Vec<String>, String> {
        self.check_with(self.implementation)
    }

    fn check_with(&mut self, implementation: &Implementation) -> Result<Vec<String>, String> {
        let output =
            self.invoke_with(implementation, &["check", "--json", &self.test.target], b"")?;
        let diagnostics = protocol::check_report(output)?;
        Ok(judge::diagnostics(&self.spec.diagnostics, &diagnostics))
    }

    fn test_blocks(&mut self) -> Result<Vec<String>, String> {
        let output = self.invoke(&["test", "--json", &self.test.target], b"")?;
        let report = protocol::test_report(output)?;
        let reasons = judge::diagnostics(&self.spec.diagnostics, &report.diagnostics);
        if !reasons.is_empty() {
            return Ok(reasons);
        }
        let Kind::TestBlocks(expected) = &self.spec.kind else {
            unreachable!("only test-block tests call `test`");
        };
        Ok(judge::tests(expected, &report.tests))
    }

    fn run(&mut self, run: &RunSpec) -> Result<Vec<String>, String> {
        let reasons = self.check()?;
        if !reasons.is_empty() {
            return Ok(reasons);
        }
        let mut args = vec!["run", self.test.target.as_str()];
        args.extend(run.args.iter().map(String::as_str));
        let implementation = self.implementation;
        let output = self.invoke(&args, &run.stdin)?;
        if implementation.declined(output) {
            return Ok(vec![DECLINED.to_owned()]);
        }
        if !implementation.locates() {
            let unlocated = RunSpec {
                panic_at: None,
                ..run.clone()
            };
            return Ok(judge::run(&unlocated, output));
        }
        Ok(judge::run(run, output))
    }

    /// Checks the program under both implementations, then runs it under both and compares
    /// the runs, with what `also` requires besides. When it compares the tests, it runs them
    /// first, since `test --json` reports the diagnostics that `check --json` would, which
    /// spares a command on each side.
    fn differential(
        &mut self,
        run: &RunSpec,
        other: &Implementation,
        also: Also,
    ) -> Result<Vec<String>, String> {
        let tested = if also.tests {
            Some((self.tested(self.implementation)?, self.tested(other)?))
        } else {
            None
        };
        let mut reasons = if let Some((here, there)) = &tested {
            let mut reasons = judge::diagnostics(&self.spec.diagnostics, &here.report.diagnostics);
            reasons.extend(elsewhere(judge::diagnostics(
                &self.spec.diagnostics,
                &there.report.diagnostics,
            )));
            reasons
        } else {
            let mut reasons = self.check()?;
            reasons.extend(elsewhere(self.check_with(other)?));
            reasons
        };
        if !reasons.is_empty() {
            return Ok(reasons);
        }
        let mut args = vec!["run", self.test.target.as_str()];
        args.extend(run.args.iter().map(String::as_str));
        self.invoke(&args, &run.stdin)?;
        self.invoke_with(other, &args, &run.stdin)?;
        let [.., first, second] = self.steps.as_slice() else {
            unreachable!("both runs were recorded");
        };
        reasons = judge::same_run(&first.output, &second.output);
        reasons.extend(judge::unexpected_abort(run, &first.output, &second.output));
        if also.succeeds && reasons.is_empty() {
            reasons.extend(judge::unsuccessful(&first.output));
        }
        if let Some((here, there)) = &tested {
            reasons.extend(same_tests(here, there));
        }
        Ok(reasons)
    }

    /// What `test --json` reports for the program under `implementation`.
    fn tested(&mut self, implementation: &Implementation) -> Result<Tested, String> {
        let args = ["test", "--json", self.test.target.as_str()];
        let output = self.invoke_with(implementation, &args, b"")?;
        Ok(Tested {
            report: protocol::test_report(output)?,
            verdicts: protocol::property_verdicts(output)?,
        })
    }

    fn invoke(&mut self, args: &[&str], stdin: &[u8]) -> Result<&Output, String> {
        self.invoke_with(self.implementation, args, stdin)
    }

    fn invoke_with(
        &mut self,
        implementation: &Implementation,
        args: &[&str],
        stdin: &[u8],
    ) -> Result<&Output, String> {
        let step = implementation.invoke(self.test, args, stdin)?;
        self.steps.push(step);
        Ok(&self.steps[self.steps.len() - 1].output)
    }
}

/// What `test --json` reported: the program's diagnostics and its tests' results, with the
/// verdicts of its properties.
struct Tested {
    report: protocol::TestReport,
    verdicts: protocol::Verdicts,
}

/// The reasons that the other implementation's commands gave.
fn elsewhere(reasons: Vec<String>) -> impl Iterator<Item = String> {
    reasons
        .into_iter()
        .map(|reason| format!("{reason} under the other implementation"))
}

/// Where the properties' verdicts of two implementations differ, each way.
fn same_verdicts(here: &Tested, there: &Tested) -> Vec<String> {
    let mut reasons: Vec<String> = here
        .verdicts
        .iter()
        .filter_map(|(at, v)| {
            let w = there.verdicts.iter().find(|(a, _)| a == at).map(|(_, w)| w);
            (w != Some(v)).then(|| {
                let w = w.map_or_else(|| "none".to_owned(), ToString::to_string);
                format!(
                    "the property at {}:{} gives {v}, and {w} under the other implementation",
                    at.0, at.1
                )
            })
        })
        .collect();
    reasons.extend(
        there
            .verdicts
            .iter()
            .filter(|(at, _)| !here.verdicts.iter().any(|(a, _)| a == at))
            .map(|(at, w)| {
                format!(
                    "the property at {}:{} gives none, and {w} under the other implementation",
                    at.0, at.1
                )
            }),
    );
    reasons
}

/// Compares the results of the program's tests under both implementations, and the verdicts
/// of their properties (tests.property-verdict).
fn same_tests(here: &Tested, there: &Tested) -> Vec<String> {
    let mut reasons = same_verdicts(here, there);
    let (here, there) = (&here.report.tests, &there.report.tests);
    for got in here {
        match there
            .iter()
            .find(|t| t.file == got.file && t.line == got.line)
        {
            Some(t) if t.passed != got.passed => reasons.push(format!(
                "the test at {}:{} {}, and {} under the other implementation",
                got.file,
                got.line,
                verb(got.passed),
                verb(t.passed)
            )),
            Some(_) => {}
            None => reasons.push(format!(
                "the test at {}:{} has a result only here",
                got.file, got.line
            )),
        }
    }
    for t in there {
        if !here
            .iter()
            .any(|got| got.file == t.file && got.line == t.line)
        {
            reasons.push(format!(
                "the test at {}:{} has a result only under the other implementation",
                t.file, t.line
            ));
        }
    }
    reasons
}

/// How a test ended, as a verb.
fn verb(passed: bool) -> &'static str {
    if passed { "passed" } else { "failed" }
}

/// What a test is compared with under another implementation, whatever it expects.
#[derive(Clone, Copy)]
enum Compared<'a> {
    Trees,
    Checks(Option<&'a BTreeSet<String>>),
    Runs,
}

/// The run that a test's annotations give, if they can be read and give one.
fn given(case: &Case) -> Option<&RunSpec> {
    match &case.spec {
        Ok(Spec {
            kind: Kind::Run(run),
            ..
        }) => Some(run),
        _ => None,
    }
}

/// Runs the program under both implementations, with the arguments and input of `given`, or
/// none, and compares the runs as runs of a program that may have errors.
fn runs(
    implementation: &Implementation,
    other: &Implementation,
    test: &Test,
    given: Option<&RunSpec>,
    steps: &mut Vec<Step>,
) -> Result<Vec<String>, String> {
    let mut args = vec!["run", test.target.as_str()];
    let mut stdin: &[u8] = b"";
    if let Some(run) = given {
        args.extend(run.args.iter().map(String::as_str));
        stdin = &run.stdin;
    }
    steps.push(implementation.invoke(test, &args, stdin)?);
    steps.push(other.invoke(test, &args, stdin)?);
    Ok(judge::alike_run(&steps[0].output, &steps[1].output))
}

/// Parses the program under both implementations, and compares the trees.
fn trees(
    implementation: &Implementation,
    other: &Implementation,
    test: &Test,
    steps: &mut Vec<Step>,
) -> Result<Vec<String>, String> {
    let args = ["parse", "--sexp", test.target.as_str()];
    steps.push(implementation.invoke(test, &args, b"")?);
    steps.push(other.invoke(test, &args, b"")?);
    Ok(judge::same_parse(&steps[0].output, &steps[1].output))
}

/// Checks the program under both implementations, and compares the diagnostics, or only those
/// of `codes` when they are given.
fn checks(
    implementation: &Implementation,
    other: &Implementation,
    codes: Option<&BTreeSet<String>>,
    test: &Test,
    steps: &mut Vec<Step>,
) -> Result<Vec<String>, String> {
    let args = ["check", "--json", test.target.as_str()];
    let mut report = |implementation: &Implementation| {
        steps.push(implementation.invoke(test, &args, b"")?);
        let mut diagnostics: Vec<protocol::Placed> =
            protocol::check_report(&steps[steps.len() - 1].output)?;
        diagnostics.retain(|d| codes.is_none_or(|codes| codes.contains(&d.code)));
        Ok::<_, String>(diagnostics)
    };
    let here = report(implementation)?;
    let there = report(other)?;
    Ok(judge::same_check(&here, &there))
}

/// Writes out what a test expects, for the failure log.
fn describe(spec: &Spec) -> String {
    let mut text = String::new();
    if !spec.rules.is_empty() {
        let _ = writeln!(text, "rules: {}", spec.rules.join(", "));
    }
    for diagnostic in &spec.diagnostics {
        let _ = writeln!(text, "diagnostic: {diagnostic}");
    }
    match &spec.kind {
        Kind::Check => {}
        Kind::TestBlocks(results) => {
            for result in results {
                let entry = if result.passed { "PASS" } else { "FAIL" };
                let _ = writeln!(text, "test: {}:{} {entry}", result.file, result.line);
            }
        }
        Kind::Run(run) => {
            let _ = writeln!(text, "args: {:?}", run.args);
            let _ = writeln!(text, "exit status: {}", run.exit);
            if let Some(kind) = &run.panic {
                let _ = writeln!(text, "panic: {kind}");
            }
            let _ = writeln!(text, "--- stdout\n{}", run.stdout);
            if let Some(stderr) = &run.stderr {
                let _ = writeln!(text, "--- stderr\n{stderr}");
            }
        }
    }
    text
}
