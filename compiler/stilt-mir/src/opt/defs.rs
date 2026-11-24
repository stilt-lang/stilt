//! Where a function's locals get their values.

use crate::mir::{Function, Rvalue, Stmt, Terminator};

/// How many times each local is defined: once for a parameter, and once for each assignment
/// and each call that gives it a value.
#[must_use]
pub fn definitions(f: &Function) -> Vec<usize> {
    let mut defs = vec![0; f.locals.len()];
    for p in &f.params {
        defs[p.local.0 as usize] += 1;
    }
    for block in &f.blocks {
        for s in &block.stmts {
            if let Stmt::Assign(d, _) = s {
                defs[d.0 as usize] += 1;
            }
        }
        if let Terminator::Call { dest, raised, .. } = &block.term {
            for d in dest.iter().chain(raised.iter().flat_map(|(e, _)| e)) {
                defs[d.0 as usize] += 1;
            }
        }
    }
    defs
}

/// The rvalue that defines each local defined once, by an assignment.
pub(crate) fn defined_once(f: &Function) -> Vec<Option<&Rvalue>> {
    let defs = definitions(f);
    let mut by: Vec<Option<&Rvalue>> = vec![None; f.locals.len()];
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        if let Stmt::Assign(d, r) = s
            && defs[d.0 as usize] == 1
        {
            by[d.0 as usize] = Some(r);
        }
    }
    by
}
