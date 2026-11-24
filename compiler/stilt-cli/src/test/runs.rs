//! Running the cases of a plan: those without a cached result, compiled into one image and run
//! one after another, each on a thread of its own, and each run of a property's closure on one of
//! its own (program.running-tests; tests.running-cases). When every test that ran passed, no thread
//! holds an object, so once the constants are released every count must be back to zero, as at the
//! end of a run (goal no-leaks).

use std::path::Path;

use stilt_codegen_clif::Image;
use stilt_runtime::{Note, Tested};

use super::plan::{Kind, Why};
use super::{Plan, Ran, prop};

/// The results of a plan's cases, and the exit status of a debug build that leaks, when every
/// test that ran passed and some object outlived them.
pub(super) struct Results {
    pub(super) ran: Vec<Ran>,
    pub(super) leaked: Option<i32>,
}

/// The result of each case of `plan`, of the program at `path`: its cached result, or the
/// result of running it. A stack overflow or running out of memory ends the process instead,
/// with status 134 (program.test-results).
pub(super) fn results(path: &Path, plan: &Plan) -> Result<Results, String> {
    if plan.cases.iter().all(|c| c.cached.is_some()) {
        let ran = plan.cases.iter().filter_map(|c| c.cached.clone()).collect();
        return Ok(Results { ran, leaked: None });
    }
    let mut image = Image::new()?;
    image.set_files(crate::run::paths(path));
    image.set_guards(plan.guards.clone());
    image.load(&plan.functions)?;
    stilt_runtime::prepare_tests(plan.files.clone());
    let mut ran = Vec::with_capacity(plan.cases.len());
    let mut ran_passed = true;
    for case in &plan.cases {
        let result = if let Some(result) = &case.cached {
            result.clone()
        } else {
            let entry = image.entry_of(&case.entry)?;
            let result = match &case.property {
                Some(spec) => {
                    let verdict = prop::run(entry, spec);
                    Ran {
                        passed: verdict.failed.is_none(),
                        property: Some(verdict),
                        why: None,
                    }
                }
                None => outcome(case.kind, stilt_runtime::test(entry)),
            };
            ran_passed &= result.passed;
            result
        };
        ran.push(result);
    }
    let leaked = if ran_passed {
        image.release_constants();
        stilt_runtime::leaked()
    } else {
        None
    };
    // A test that panicked or called `exit` left its thread waiting with the image's code on
    // its stack, so the image lasts until the process ends.
    std::mem::forget(image);
    Ok(Results { ran, leaked })
}

/// The result of a test or a doc example that ended as `tested` says.
fn outcome(kind: Kind, tested: Tested) -> Ran {
    let why = if tested.passed {
        None
    } else {
        Some(match (tested.report, tested.note) {
            (Some(report), _) => Why::Panicked(report),
            (None, Some(Note::Raised(shown))) => Why::Raised(shown),
            (None, Some(Note::Compared(left, right))) => Why::Compared(left, right),
            (None, None) if !tested.returned => Why::Exited,
            (None, None) => Why::False,
        })
    };
    let why = why.filter(|_| kind != Kind::Property);
    Ran {
        passed: tested.passed,
        property: None,
        why,
    }
}
