//! `stilt test`: runs every test, doc example and property of a program without errors, and
//! reports a result for each (program.running-tests and program.doc-examples;
//! conformance.test-objects; tests.property-results).
//!
//! - **The engine.** `test` asks the program's engine, a program of one file included, starting
//!   one when none runs (goal one-engine). The engine checks the program and lowers the
//!   entries of its tests, which `test` compiles and runs in its own process, then tells the
//!   engine the results, so that it remembers them. With no engine to answer, `test` holds the
//!   program in a database of its own, and remembers nothing.
//! - **Isolation.** The tests run one after another in one image, each on a thread of its own
//!   (`stilt_runtime::test`). A panic or an `exit` ends only its thread, whose test fails: the
//!   thread then waits until the process ends, with the objects it held. A stack overflow or
//!   running out of memory ends the process, after `fatal: <reason>`, with status 134, so that
//!   no test reports a result. Running every test in one process compiles the program once,
//!   where a process for each test would start, and compile, once a test.
//! - **Cached results.** A test whose code, and the code of every function that its entry
//!   reaches, hashes as it did in an earlier run that the engine answered, and that doesn't do
//!   `io`, takes its result from that run without running ([`plan::Memory`]).
//! - **The verdict.** With `--json`, `test` writes one object: the diagnostics and the results
//!   of conformance.diagnostic-objects and conformance.test-objects, with `done` when there are no errors and every test passed (goal one-verdict),
//!   and `repeat` when the program's files are those of an earlier run whose verdict wasn't
//!   done (repeated-failures-flagged). Without it, stdout holds each failure, with its place, what it was and why it
//!   failed, then one line that counts the results, after the diagnostics on stderr
//!   ([`render`]). The status is 0 when the verdict is done, and 1 otherwise. What the tests
//!   print goes to stderr, and so do the panic reports of the tests with `--json`.
//! - **Leaks.** When every test that ran passed, `test` releases the constants they computed and
//!   checks that every count is back to zero, as a run does at its end, reporting the objects
//!   never freed with the status of a debug build that leaks (goal no-leaks).

mod plan;
mod prop;
mod render;
mod runs;

use std::path::Path;

use serde_json::json;
use stilt_db::Database;
use stilt_rc::Counted;

pub(crate) use plan::{Memory, Plan, Ran, done, plan, plan_std};

use crate::engine::Tests;
use crate::report::Report;

/// Runs the tests of the program at `path`, and reports them.
pub(crate) fn report(path: &Path, json: bool) -> Report {
    let (plan, engine) = match Tests::plan(path, json) {
        Some((engine, plan)) => (plan, Some(engine)),
        None => match here(path, json) {
            Ok(plan) => (plan, None),
            Err(message) => return Report::refuse(&message),
        },
    };
    let results = match runs::results(path, &plan) {
        Ok(results) => results,
        Err(message) => return Report::refuse(&crate::bug::internal(message)),
    };
    if let Some(engine) = engine {
        engine.record(&results.ran);
    }
    let mut report = verdict(&plan, &results.ran, json);
    if let Some(status) = results.leaked {
        report.status = u8::try_from(status).unwrap_or(1);
    }
    report
}

/// Runs every test of the program at `path` in this process, in code that counts what a profile
/// counts, reports them, and adds the counts to the program's profile (builds.profiles). A run that
/// ends with status 134 ends the process, and writes nothing.
pub(crate) fn report_profiled(path: &Path, json: bool) -> Report {
    if let Err(report) = crate::profile::read(path) {
        return report;
    }
    stilt_mir::profiling::set_profiling(stilt_mir::profiling::Profiling::Count);
    let db = Database::default();
    let program = match crate::packages::load(&db, path) {
        Ok(program) => program,
        Err(message) => return Report::refuse(&message),
    };
    let plan = plan(
        &db,
        program,
        json,
        &mut Counted::default(),
        &Memory::default(),
    )
    .0;
    let results = match runs::results(path, &plan) {
        Ok(results) => results,
        Err(message) => return Report::refuse(&crate::bug::internal(message)),
    };
    let mut report = verdict(&plan, &results.ran, json);
    if let Some(status) = results.leaked {
        report.status = u8::try_from(status).unwrap_or(1);
    }
    let counted = stilt_runtime::profile::take();
    if let Err(refused) = crate::profile::add(path, &db, program, &counted) {
        return refused;
    }
    crate::end(db);
    report
}

/// Runs the standard library's own tests and doc examples, with the program at `path` around
/// them, in this process, and reports them (std.examples).
pub(crate) fn report_std(path: &Path, json: bool) -> Report {
    let db = Database::default();
    let planned = crate::packages::load(&db, path).map(|program| plan_std(&db, program, json));
    crate::end(db);
    let plan = match planned {
        Ok(plan) => plan,
        Err(message) => return Report::refuse(&message),
    };
    match runs::results(path, &plan) {
        Ok(results) => verdict(&plan, &results.ran, json),
        Err(message) => Report::refuse(&crate::bug::internal(message)),
    }
}

/// The plan of the program at `path`, held in a database of this process.
fn here(path: &Path, json: bool) -> Result<Plan, String> {
    let db = Database::default();
    let planned = crate::packages::load(&db, path).map(|program| {
        let memory = Memory::default();
        plan(&db, program, json, &mut Counted::default(), &memory).0
    });
    crate::end(db);
    planned
}

/// The verdict on a program whose tests gave `results`, one for each case.
fn verdict(plan: &Plan, results: &[Ran], json: bool) -> Report {
    let done = done(plan.errors, results);
    let status = u8::from(!done);
    let cases = plan.cases.iter().zip(results);
    if json {
        let diagnostics: serde_json::Value =
            serde_json::from_str(&plan.diagnostics).unwrap_or_else(|_| json!([]));
        let tests: Vec<serde_json::Value> = cases
            .map(|(c, r)| {
                let mut t = json!({
                    "file": c.file,
                    "line": c.line,
                    "passed": r.passed,
                    "kind": render::kind(c),
                    "name": c.name,
                });
                if let Some(p) = &r.property {
                    t["property"] = p.json();
                }
                if !r.passed {
                    t["why"] = json!(render::reasons(c, r));
                }
                t
            })
            .collect();
        let verdict = json!({
            "done": done,
            "repeat": plan.repeat,
            "diagnostics": diagnostics,
            "tests": tests,
        });
        return Report {
            stdout: format!("{verdict}\n"),
            stderr: render::reports(&plan.cases, results),
            status,
        };
    }
    Report {
        stdout: render::text(&plan.cases, results, plan.errors),
        stderr: plan.diagnostics.clone(),
        status,
    }
}
