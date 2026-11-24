//! What a program's roots reach, with its reference counting, followed from one version of the
//! program to the next, so that an update counts, and gives, only what an edit changed (goal
//! edit-to-running-program).
//!
//! A function's code follows its MIR and the parameters that it and the functions it calls directly
//! consume (values.consumed-parameters). What a function consumes follows only its own body's
//! [`Summary`] and those of the functions it passes a parameter to, which it calls directly, so
//! what the functions reached consume follows only their own summaries, and a summary only its
//! function's MIR. When an edit leaves what is reached as it was, and the summary of each function
//! whose lowering ran again, every function reached consumes what it consumed, and the update reads
//! no other function's summary.

use std::sync::Arc;

use stilt_db::{Db, Program};
use stilt_mir::mir::Function;
use stilt_mir::{CheckErrors, FnRef, Renewed, Walk, Walked, inline_reached};

use crate::cache::Counted;
use crate::consume::{Summary, summary};
use crate::queries::{Consumption, consumption_of, conventions_by, inferred};

/// The last walk of a program for one image, and what every function consumed then.
#[derive(Debug, Default)]
pub struct Reach {
    walk: Walk,
    consumption: Option<Arc<Consumption>>,
}

impl Reach {
    /// The functions that `roots` reach, with their reference counting from `counted`, that
    /// may differ from those this gave last: on the first update, after one with errors, and
    /// with errors, every function reached; when what a function consumes changed, which
    /// changes the code of its callers, every function reached too; and otherwise those that
    /// [`Walk::walk`] tells may differ, every other function keeping the code it was given.
    pub fn update<D: Db + Clone>(
        &mut self,
        db: &D,
        program: Program,
        roots: Vec<FnRef>,
        errors: &CheckErrors,
        counted: &mut Counted,
    ) -> Vec<Arc<Function>> {
        let walked = self.walk.walk(db, program, roots, errors);
        let (functions, now) = match &self.consumption {
            Some(last) if consume_as_before(&walked, &self.walk) => {
                let renewed = inline_reached(db, program, walked.renewed().to_vec());
                let functions =
                    counted.insert_by(renewed, |f| conventions_by(db, program, last, f));
                (functions, Arc::clone(last))
            }
            _ => self.count(db, program, &walked, counted),
        };
        // Kept once nothing reads the database any more, so that an edit that cancels the
        // update leaves the last walk as it was.
        self.walk.keep(walked);
        self.consumption = Some(now);
        functions
    }

    /// The functions that `walked` tells may differ, or every function it reached when what a
    /// function consumes changed, counted by what each consumes now, which the summary of every
    /// function reached is read for, across the machine's cores first.
    fn count<D: Db + Clone>(
        &self,
        db: &D,
        program: Program,
        walked: &Walked,
        counted: &mut Counted,
    ) -> (Vec<Arc<Function>>, Arc<Consumption>) {
        let reached = walked.functions(&self.walk);
        let mut now = consumption_of(db, program, &reached, &Consumption::new());
        let same = self
            .consumption
            .as_ref()
            .is_some_and(|c| consume_alike(c, &now));
        let functions = if same {
            walked.renewed().to_vec()
        } else {
            reached
        };
        let functions = inline_reached(db, program, functions);
        // Inlining makes a function call what the functions it inlines call, which the walk
        // reached, so this finds nothing unless inlining calls what nothing reached named.
        let more = consumption_of(db, program, &functions, &now);
        now.extend(more);
        (
            counted.insert_by(functions, |f| conventions_by(db, program, &now, f)),
            Arc::new(now),
        )
    }
}

/// Whether `walked` reached what `last` did, and each function whose lowering ran again has the
/// summary it had, so that every function reached consumes what it consumed.
fn consume_as_before(walked: &Walked, last: &Walk) -> bool {
    walked.renewals(last).is_some_and(|renewals| {
        renewals.iter().all(|r: &Renewed<'_>| {
            !inferred(r.f) || summary_of(r.f, r.before) == summary_of(r.f, r.now)
        })
    })
}

/// The summary of the function named `f` among `functions`.
fn summary_of(f: &FnRef, functions: &[Arc<Function>]) -> Option<Summary> {
    functions.iter().find(|g| g.name == *f).map(|g| summary(g))
}

/// Whether every function consumes the same parameters by `a` as by `b`, a function that
/// either leaves out consuming none, as [`crate::consumed`] reads them.
fn consume_alike(a: &Consumption, b: &Consumption) -> bool {
    let within = |a: &Consumption, b: &Consumption| {
        a.iter()
            .all(|(f, c)| b.get(f).map_or(c.is_empty(), |d| d == c))
    };
    within(a, b) && within(b, a)
}

#[cfg(test)]
mod tests;
