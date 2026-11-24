//! The checks that verification proves can't fail (facts.verification), which a release build drops
//! (builds.dropped-checks). Lowering marks the location word of each such operation
//! ([`PROVED_CHECK`], [`PROVED_OVERFLOW`]), and a debug build reads no mark. A proved read or
//! slot of a list's element becomes its form that checks nothing, and a proved check of a number
//! or of an array's index a condition that clang takes as false, so that it drops the test and
//! knows what the test ruled out.

use std::sync::Arc;

use stilt_mir::mir::{
    Const, Function, Operand, PROVED_CHECK, PROVED_OVERFLOW, Runtime, Rvalue, Stmt,
};

use crate::prim::{DIVIDE_BY_ZERO, OVERFLOW};

/// The runtime's number of the panic of an index out of bounds (effects.panic-kinds).
const BOUNDS: u64 = 2;

/// Which checks of an operation verification proves, by the marks of its location.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Proved {
    /// Its check of an index or of a divisor.
    check: bool,
    /// Its check of overflow.
    overflow: bool,
}

impl Proved {
    pub(crate) fn of(loc: &Operand) -> Self {
        match loc {
            Operand::Const(Const::Word(w)) => Self {
                check: w & PROVED_CHECK != 0,
                overflow: w & PROVED_OVERFLOW != 0,
            },
            _ => Self::default(),
        }
    }

    /// Whether the check that panics with the runtime's kind `kind` is proved.
    pub(crate) fn rules_out(self, kind: u64) -> bool {
        match kind {
            OVERFLOW => self.overflow,
            DIVIDE_BY_ZERO | BOUNDS => self.check,
            _ => false,
        }
    }
}

/// `f` with each read and slot of a list's element whose index is proved in bounds made one
/// that checks nothing.
pub(crate) fn unchecked_lists(f: &Arc<Function>) -> Arc<Function> {
    let proved = |s: &Stmt| matches!(s, Stmt::Assign(_, Rvalue::Runtime(op, args)) if unchecked(*op).is_some() && Proved::of(&args[0]).check);
    if !f.blocks.iter().flat_map(|b| &b.stmts).any(proved) {
        return Arc::clone(f);
    }
    let mut f = Function::clone(f);
    for s in f.blocks.iter_mut().flat_map(|b| &mut b.stmts) {
        if !proved(s) {
            continue;
        }
        if let Stmt::Assign(_, Rvalue::Runtime(op, args)) = s
            && let Some(form) = unchecked(*op)
        {
            *op = form;
            args.remove(0);
        }
    }
    Arc::new(f)
}

/// The form of a list's operation that checks no index, for one that checks it.
fn unchecked(op: Runtime) -> Option<Runtime> {
    match op {
        Runtime::ListIndex => Some(Runtime::ListAt),
        Runtime::ListSlot => Some(Runtime::ListSlotAt),
        Runtime::ListElement => Some(Runtime::ListElementAt),
        _ => None,
    }
}
