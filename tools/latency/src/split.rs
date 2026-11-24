//! Where an update's time goes (goals edit-to-diagnostics, edit-to-running-program and one-engine),
//! in four parts:
//!
//! - validation: the same update timed again after a revision that changed nothing, so that
//!   every query it reads is proved unchanged and none runs: salsa checking what each memo read,
//!   and for a patch, the walk over the program's functions that finds the changed ones;
//! - analysis: the rest of the front end's time, its queries that run again;
//! - code generation: the rest of the time to the compiled code: lowering to MIR, reference
//!   counting and Cranelift;
//! - patching: making the compiled code live, its memory executable and its slots set, and
//!   comparing the layouts of the program's values.

use std::time::Duration;

use crate::millis;
use crate::script::Kind;

/// The parts of one update.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Split {
    pub(crate) validation: Duration,
    pub(crate) analysis: Duration,
    pub(crate) codegen: Duration,
    pub(crate) patching: Duration,
}

impl Split {
    /// The split of a front end that took `front` in the update, and `validation` when
    /// nothing had changed.
    pub(crate) fn front_end(front: Duration, validation: Duration) -> Self {
        let validation = validation.min(front);
        Self {
            validation,
            analysis: front.saturating_sub(validation),
            ..Self::default()
        }
    }
}

/// Prints the mean of each part over each kind's updates, and over all of them.
pub(crate) fn report(steps: &[(Kind, Split)], with_code: bool) {
    let mut kinds: Vec<Kind> = steps.iter().map(|(k, _)| *k).collect();
    kinds.sort();
    kinds.dedup();
    print!("mean ms     validation   analysis");
    if with_code {
        print!("   code generation   patching");
    }
    println!();
    let rows = kinds
        .iter()
        .map(|&kind| (kind.name(), Some(kind)))
        .chain([("all", None)]);
    for (name, kind) in rows {
        let of: Vec<&Split> = steps
            .iter()
            .filter(|(k, _)| kind.is_none_or(|kind| *k == kind))
            .map(|(_, s)| s)
            .collect();
        let mean = |part: fn(&Split) -> Duration| {
            let total: Duration = of.iter().map(|s| part(s)).sum();
            millis(total) / f64::from(u32::try_from(of.len().max(1)).unwrap_or(u32::MAX))
        };
        print!(
            "{name:<10} {:>11.1} {:>10.1}",
            mean(|s| s.validation),
            mean(|s| s.analysis)
        );
        if with_code {
            print!(
                " {:>17.1} {:>10.1}",
                mean(|s| s.codegen),
                mean(|s| s.patching)
            );
        }
        println!();
    }
}
