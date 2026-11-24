//! Copies that inlining leaves: a parameter's argument copied into the body, the words of an
//! object read through its fields, a result copied into the call's locals. A local that the
//! source doesn't name, defined once by a copy of a local that is itself defined once, holds
//! what that local holds wherever it is read, so its reads read that local instead and the copy
//! goes, which leaves the passes after it, and Cranelift, less code to read. The value keeps its
//! references: the copy would have taken the local's, and the local now keeps it until its last
//! use, as reference counting decides.

use crate::mir::{Function, Local, Operand, Rvalue, Stmt};
use crate::opt::defs::definitions;
use crate::opt::inline::rename::Renaming;

/// Replaces each such copy of `f` by the local it copies.
pub(crate) fn propagate(f: &mut Function) {
    let defs = definitions(f);
    let once = |l: Local| defs[l.0 as usize] == 1 && !f.locals[l.0 as usize].slot;
    let params: Vec<Local> = f.params.iter().map(|p| p.local).collect();
    let mut source: Vec<Option<Local>> = vec![None; f.locals.len()];
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        if let Stmt::Assign(d, Rvalue::Use(Operand::Local(s))) = s
            && once(*d)
            && once(*s)
            && !params.contains(d)
            && f.locals[d.0 as usize].name.is_none()
            && f.locals[d.0 as usize].repr == f.locals[s.0 as usize].repr
        {
            source[d.0 as usize] = Some(*s);
        }
    }
    if source.iter().all(Option::is_none) {
        return;
    }
    let locals = (0..f.locals.len())
        .map(|l| Operand::Local(root(&source, Local(u32::try_from(l).expect("under 4G")))))
        .collect();
    let renaming = Renaming { locals, blocks: 0 };
    for d in &mut f.locals {
        d.repr = renaming
            .repr(d.repr)
            .expect("every local is renamed to a local");
    }
    for block in &mut f.blocks {
        let stmts = std::mem::take(&mut block.stmts);
        block.stmts = stmts
            .iter()
            .filter(|s| !matches!(s, Stmt::Assign(d, _) if source[d.0 as usize].is_some()))
            .map(|s| renaming.stmt(s).expect("every local is renamed to a local"))
            .collect();
        block.term = renaming
            .term(&block.term)
            .expect("every local is renamed to a local");
    }
}

/// The local that `l` copies, through copies, or `l` itself.
fn root(source: &[Option<Local>], mut l: Local) -> Local {
    // Each copy's source is defined before it, so the chain ends; the bound only guards it.
    for _ in 0..source.len() {
        match source[l.0 as usize] {
            Some(s) => l = s,
            None => break,
        }
    }
    l
}
