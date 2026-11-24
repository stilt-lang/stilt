//! Which locals are C `double`s: those that hold an `f64` (`stilt_mir::floats`), as for
//! Cranelift's `F64` variables, but for a local in memory, which stays a word and is converted
//! where an operation reads it. A conversion keeps every bit, so the choice decides where values
//! live, never what a program computes.

use stilt_mir::mir::Function;

/// Whether each local of `f` is a `double`.
pub(crate) fn double_locals(f: &Function) -> Vec<bool> {
    let floats = stilt_mir::floats::f64_locals(f);
    (floats.into_iter().zip(&f.locals))
        .map(|(float, decl)| float && !decl.slot)
        .collect()
}
