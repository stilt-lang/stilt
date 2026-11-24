//! The command-line protocol between the runner and an implementation (conformance.commands and
//! conformance.run-statuses).

use std::ffi::OsString;
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use serde::Deserialize;

use crate::cache::Cache;
use crate::discovery::Test;
use crate::process::{self, Output, Status};

/// A diagnostic as conformance compares it: a code on a line of a file.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
pub(crate) struct Diagnostic {
    pub(crate) code: String,
    pub(crate) file: String,
    pub(crate) line: usize,
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}:{}", self.code, self.file, self.line)
    }
}

/// A diagnostic as two implementations' checks are compared: a code at a line and column of
/// a file.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
pub(crate) struct Placed {
    pub(crate) code: String,
    pub(crate) file: String,
    pub(crate) line: usize,
    pub(crate) col: usize,
}

impl fmt::Display for Placed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} at {}:{}:{}",
            self.code, self.file, self.line, self.col
        )
    }
}

/// A diagnostic of a report, which is an error or a warning.
pub(crate) trait Reported: for<'de> Deserialize<'de> {
    fn code(&self) -> &str;

    fn is_error(&self) -> bool {
        self.code().starts_with('E')
    }
}

impl Reported for Diagnostic {
    fn code(&self) -> &str {
        &self.code
    }
}

impl Reported for Placed {
    fn code(&self) -> &str {
        &self.code
    }
}

/// The result of one test or doc example, identified by the line that declares it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
pub(crate) struct TestResult {
    pub(crate) file: String,
    pub(crate) line: usize,
    pub(crate) passed: bool,
}

/// What `IMPL test --json` reports.
#[derive(Debug, Deserialize)]
pub(crate) struct TestReport {
    pub(crate) diagnostics: Vec<Diagnostic>,
    pub(crate) tests: Vec<TestResult>,
}

#[derive(Deserialize)]
#[serde(bound = "D: Reported")]
struct CheckReport<D> {
    diagnostics: Vec<D>,
}

/// An implementation under test, started afresh for every command.
#[derive(Debug)]
pub(crate) struct Implementation {
    program: PathBuf,
    path_env: OsString,
    time_limit: Duration,
    /// Where the results of this implementation's commands are kept, if they are.
    cache: Option<Cache>,
    /// Whether the implementation may have engines: until `engine --stop` fails as a command
    /// it doesn't know, with a status other than 0, for an engine stopped, or 1, for none.
    engines: AtomicBool,
    /// The exit status by which it declines to run a program, as an implementation of part of
    /// the language does.
    declines: Option<i32>,
    /// Whether its panic reports say where the panic is (program.panic-location): the formal
    /// model's don't, so a `panic-at` isn't asked of it.
    locates: bool,
}

/// One command run during a test, kept for the failure log.
#[derive(Debug)]
pub(crate) struct Step {
    pub(crate) command: String,
    pub(crate) output: Output,
    /// The implementation, when the command ran and may have started an engine for the
    /// test's program: any command on a directory, and `test` on any program (goal
    /// one-engine).
    engine: Option<PathBuf>,
}

impl Implementation {
    /// Locates `program` the way a shell would: a name with no directory is searched for in
    /// `path_env`, and any other path is made absolute, since tests run in other directories.
    /// Each command it runs is killed after `time_limit`.
    pub(crate) fn locate(
        program: &Path,
        path_env: OsString,
        time_limit: Duration,
    ) -> Result<Self, String> {
        let found = if program.components().count() > 1 {
            program.canonicalize().ok()
        } else {
            std::env::split_paths(&path_env)
                .map(|dir| dir.join(program))
                .find(|candidate| candidate.is_file())
        };
        match found {
            Some(program) => Ok(Self {
                program,
                path_env,
                time_limit,
                cache: None,
                engines: AtomicBool::new(true),
                declines: None,
                locates: true,
            }),
            None => Err(format!(
                "cannot find the implementation `{}`",
                program.display()
            )),
        }
    }

    /// Keeps the results of this implementation's commands in `dir`, and answers a command
    /// from there when its binary and program are as they were (the cache's module says why
    /// that is safe).
    pub(crate) fn cached_in(mut self, dir: &Path) -> Result<Self, String> {
        self.cache = Some(Cache::open(dir, &self.program)?);
        Ok(self)
    }

    /// Declines to run the programs whose `run` ends with `status`.
    pub(crate) fn declining(mut self, status: Option<i32>) -> Self {
        self.declines = status;
        self
    }

    /// Asks no `panic-at` of this implementation when `unlocated`, as one whose panic reports
    /// name no place.
    pub(crate) fn locating(mut self, unlocated: bool) -> Self {
        self.locates = !unlocated;
        self
    }

    /// Whether its panic reports say where the panic is.
    pub(crate) fn locates(&self) -> bool {
        self.locates
    }

    /// Whether a `run` that ended so declined to run its program.
    pub(crate) fn declined(&self, output: &Output) -> bool {
        self.declines
            .is_some_and(|status| output.status == crate::process::Status::Exited(status))
    }

    /// Stops the engine that this implementation's commands on `test`, run as `steps`, may
    /// have started (goal one-engine), so that none outlives the test. The commands of a
    /// test share its engine: each one after the first is answered by the engine the first
    /// started, as it would be for a programmer who runs them in turn, and a stop after each
    /// would start an engine, and load the program, once a command. An implementation with no
    /// engine fails at once, and isn't asked again.
    pub(crate) fn stop_engine(&self, test: &Test, steps: &[Step]) {
        if !self.engines.load(Ordering::Relaxed)
            || !steps
                .iter()
                .any(|step| step.engine.as_ref() == Some(&self.program))
        {
            return;
        }
        let status = std::process::Command::new(&self.program)
            .args(["engine", "--stop", &test.target])
            .current_dir(&test.dir)
            .env_clear()
            .env("PATH", &self.path_env)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
        if status.is_ok_and(|status| !matches!(status.code(), Some(0 | 1))) {
            self.engines.store(false, Ordering::Relaxed);
        }
    }

    /// Runs one command of the protocol in the test's working directory.
    pub(crate) fn invoke(&self, test: &Test, args: &[&str], stdin: &[u8]) -> Result<Step, String> {
        let command = process::Command {
            program: &self.program,
            args,
            dir: &test.dir,
            stdin,
            path_env: &self.path_env,
            time_limit: self.time_limit,
        };
        let cached = self
            .cache
            .as_ref()
            .and_then(|cache| Some((cache, cache.key(test, args, stdin).ok()?)));
        if let Some(output) = cached.as_ref().and_then(|(cache, key)| cache.fetch(key)) {
            return Ok(Step {
                command: command.to_string(),
                output,
                engine: None,
            });
        }
        let output = process::run(&command)
            .map_err(|error| format!("cannot start `{}`: {error}", self.program.display()))?;
        if let Some((cache, key)) = &cached {
            cache.store(key, &output);
        }
        let engine =
            (test.target == "." || args.first() == Some(&"test")).then(|| self.program.clone());
        Ok(Step {
            command: command.to_string(),
            output,
            engine,
        })
    }
}

/// Reads the output of `IMPL check --json` and checks that its exit status agrees with it.
pub(crate) fn check_report<D: Reported>(output: &Output) -> Result<Vec<D>, String> {
    let status = finished("check", output)?;
    let report: CheckReport<D> = parse_json("check", output)?;
    let has_errors = report.diagnostics.iter().any(D::is_error);
    if status != i32::from(has_errors) {
        return Err(format!(
            "`check` exited with status {status}, which contradicts its diagnostics"
        ));
    }
    Ok(report.diagnostics)
}

/// Reads the output of `IMPL test --json` and checks that its exit status agrees with it.
pub(crate) fn test_report(output: &Output) -> Result<TestReport, String> {
    let status = finished("test", output)?;
    let report: TestReport = parse_json("test", output)?;
    let has_errors = report.diagnostics.iter().any(Diagnostic::is_error);
    if has_errors && !report.tests.is_empty() {
        return Err("`test` ran tests on a program with errors".to_owned());
    }
    let all_passed = report.tests.iter().all(|test| test.passed);
    if status != i32::from(has_errors || !all_passed) {
        return Err(format!(
            "`test` exited with status {status}, which contradicts its results"
        ));
    }
    Ok(report)
}

/// The verdicts of a program's properties, each by the file and line of its test object.
pub(crate) type Verdicts = Vec<((String, usize), serde_json::Value)>;

/// The verdict of each property that `test --json` reports, by the file and line of its test
/// object: its `property` object, without the `detail` of a panic other than `explicit`, whose
/// wording is up to each implementation (tests.property-verdict). Implementations may add the field
/// to any test object (conformance.extra-fields), so the runner compares it only between two of
/// them. A property whose test object has no file or line is an error, never skipped.
pub(crate) fn property_verdicts(output: &Output) -> Result<Verdicts, String> {
    let report: serde_json::Value = parse_json("test", output)?;
    let tests = report["tests"].as_array().cloned().unwrap_or_default();
    let mut verdicts = Vec::new();
    for t in tests {
        let Some(property) = t.get("property") else {
            continue;
        };
        let mut property = property.clone();
        let failure = property["failure"].as_str().unwrap_or("");
        if failure.starts_with("panic: ") && failure != "panic: explicit" {
            property.as_object_mut().map(|p| p.remove("detail"));
        }
        let at = t["file"]
            .as_str()
            .zip(t["line"].as_u64().and_then(|l| usize::try_from(l).ok()));
        let Some((file, line)) = at else {
            return Err(format!(
                "`test --json` reports a property with no file or line: {t}"
            ));
        };
        verdicts.push(((file.to_owned(), line), property));
    }
    Ok(verdicts)
}

fn finished(command: &str, output: &Output) -> Result<i32, String> {
    match output.status {
        Status::Exited(code) => Ok(code),
        Status::Signaled(signal) => Err(format!("`{command}` was killed by signal {signal}")),
        Status::TimedOut(_) => Err(format!("`{command}` exceeded the time limit")),
    }
}

fn parse_json<T: for<'de> Deserialize<'de>>(command: &str, output: &Output) -> Result<T, String> {
    serde_json::from_slice(&output.stdout)
        .map_err(|error| format!("`{command}` printed invalid JSON: {error}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn output(code: i32, stdout: &str) -> Output {
        Output {
            status: Status::Exited(code),
            stdout: stdout.into(),
            stderr: Vec::new(),
        }
    }

    #[test]
    fn check_report_accepts_extra_fields() {
        let json =
            r#"{"diagnostics": [{"code": "E0404", "file": "main.lt", "line": 3, "msg": "x"}]}"#;
        let diagnostics: Vec<Diagnostic> = check_report(&output(1, json)).unwrap();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].to_string(), "E0404 at main.lt:3");
    }

    #[test]
    fn check_report_rejects_a_status_that_contradicts_the_diagnostics() {
        let json = r#"{"diagnostics": [{"code": "E0001", "file": "main.lt", "line": 1}]}"#;
        assert!(check_report::<Diagnostic>(&output(0, json)).is_err());
        assert!(check_report::<Diagnostic>(&output(1, r#"{"diagnostics": []}"#)).is_err());
        let warning = r#"{"diagnostics": [{"code": "W0001", "file": "main.lt", "line": 1}]}"#;
        assert!(check_report::<Diagnostic>(&output(0, warning)).is_ok());
    }

    #[test]
    fn test_report_requires_no_tests_after_errors() {
        let json = r#"{"diagnostics": [{"code": "E0001", "file": "a.lt", "line": 1}],
                       "tests": [{"file": "a.lt", "line": 2, "passed": true}]}"#;
        assert!(test_report(&output(1, json)).is_err());
    }

    #[test]
    fn test_report_checks_the_status_against_the_results() {
        let failing =
            r#"{"diagnostics": [], "tests": [{"file": "a.lt", "line": 2, "passed": false}]}"#;
        assert!(test_report(&output(1, failing)).is_ok());
        assert!(test_report(&output(0, failing)).is_err());
    }

    #[test]
    fn reports_invalid_json() {
        let error = check_report::<Placed>(&output(0, "not json")).unwrap_err();
        assert!(error.starts_with("`check` printed invalid JSON"));
    }
}
