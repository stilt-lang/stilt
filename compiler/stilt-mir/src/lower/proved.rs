//! The marks of the checks that verification proves (facts.verification and
//! facts.what-proofs-change) on the location words of their operations: a release build drops each
//! check its mark names, and a debug build reads no mark and keeps every check (builds.same-meaning
//! and builds.dropped-checks).

use stilt_syntax::TextRange;
use stilt_types::verify::Check;

use super::Lower;
use crate::mir::{Const, Operand, PROVED_CHECK, PROVED_OVERFLOW};

impl Lower<'_> {
    /// The location of the operation at `at`, as [`Lower::loc_at`] gives it, with a mark for
    /// each of `checks` that verification proves of it. An operation of the standard library
    /// has its caller's location, and no mark.
    pub(crate) fn proved_at(&self, at: TextRange, checks: &[Check]) -> Operand {
        let loc = self.loc_at(at);
        let (Some(origin), Operand::Const(Const::Word(word))) = (&self.origin, &loc) else {
            return loc;
        };
        let marks = checks
            .iter()
            .filter(|&&c| origin.proofs.proves(at, c))
            .fold(0, |m, &c| m | mark(c));
        Operand::word(word | marks)
    }
}

/// The mark of a proved check.
fn mark(check: Check) -> u64 {
    match check {
        Check::Overflow => PROVED_OVERFLOW,
        Check::Bounds | Check::DivideByZero | Check::MissingKey => PROVED_CHECK,
    }
}
