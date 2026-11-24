//! Values that last the whole call: a parameter passed borrowed and a captured variable that a
//! closure reads from its environment hold values that outlive the call and that nothing changes
//! while it runs, since the caller keeps its reference and every change makes its object unique
//! first (values.consumed-parameters; modes.what-can-be-modified). So does what such a value holds:
//! a field of it, an element of it if it is a list, and a key or a value of it if it is a map,
//! which the value keeps alive and unchanged. A local that a `let` binds once to one of those, or
//! that copies one, borrows it instead of counting a reference to it, however far its uses reach
//! (goal debug-speed). A `for` loop over such a parameter reads it this way, and so does a
//! `match` on an element of such a list, with what its patterns bind.

use stilt_mir::mir::{Function, Local, Operand, ParamMode, Runtime, Rvalue, Stmt};

use crate::consume::definitions;
use crate::liveness::{Kinds, LocalKind};

/// The owned locals that can borrow their value because it lasts for the whole call.
pub(crate) fn inferred(f: &Function, kinds: &Kinds) -> Vec<Local> {
    let mut lasting = vec![false; f.locals.len()];
    for p in &f.params {
        if p.mode == ParamMode::Borrowed && kinds.kind(p.local) == LocalKind::Borrowed {
            lasting[p.local.0 as usize] = true;
        }
    }
    // A captured variable is read once from the closure, which outlives the call.
    for (i, decl) in f.locals.iter().enumerate() {
        lasting[i] |= decl.borrowed && decl.repr.counted();
    }
    let defs = definitions(f);
    let reads: Vec<(Local, Vec<Local>)> = f
        .blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter_map(|s| match s {
            Stmt::Assign(d, r) => Some((*d, sources(r, kinds)?)),
            _ => None,
        })
        .collect();
    let mut out = Vec::new();
    let mut changed = true;
    while changed {
        changed = false;
        for (d, from) in &reads {
            let i = d.0 as usize;
            if !lasting[i]
                && defs[i] == 1
                && kinds.kind(*d) == LocalKind::Owned
                && from.iter().all(|s| lasting[s.0 as usize])
            {
                lasting[i] = true;
                out.push(*d);
                changed = true;
            }
        }
    }
    out
}

/// The counted locals whose values an rvalue reads without changing, if it is a copy of one or
/// a read of what one holds, which lasts as long as they do. A word loaded through a pointer is
/// not one: what a slot holds can change.
fn sources(r: &Rvalue, kinds: &Kinds) -> Option<Vec<Local>> {
    let counted = |ops: &[Operand]| -> Vec<Local> {
        ops.iter()
            .filter_map(Operand::local)
            .filter(|l| kinds.kind(*l) != LocalKind::Uncounted)
            .collect()
    };
    let from = match r {
        Rvalue::Use(o) | Rvalue::Field { base: o, .. } => counted(std::slice::from_ref(o)),
        Rvalue::Runtime(Runtime::ListIndex | Runtime::ListAt | Runtime::MapWord, args) => {
            counted(args)
        }
        _ => return None,
    };
    (!from.is_empty()).then_some(from)
}
