//! Reads of constants out of loops (declarations.constant-evaluation). A constant is evaluated
//! where the program first uses it, and only a unary `-` that overflows can make that panic, so the
//! read of a constant that can't panic moves to the block before the loop, where the check of
//! whether it is evaluated runs once, not in every iteration.

use std::collections::HashSet;

use crate::mir::{Function, Local, Rvalue, Stmt};
use crate::opt::loops::{Dominators, natural_loops};

/// Moves each read of a constant that can't panic, whose local nothing else assigns, to the
/// end of the block before each loop that holds it and has one, the innermost loops first, so
/// that it leaves the outermost.
pub(crate) fn hoist(f: &mut Function) {
    let dom = Dominators::of(f);
    let once = assigned_once(f);
    for l in natural_loops(f, &dom) {
        let Some(pre) = l.preheader else { continue };
        for &b in &l.blocks {
            let (moved, kept): (Vec<Stmt>, Vec<Stmt>) = std::mem::take(&mut f.blocks[b].stmts)
                .into_iter()
                .partition(|s| {
                    matches!(s, Stmt::Assign(d, Rvalue::Constant(.., true)) if once.contains(d))
                });
            f.blocks[b].stmts = kept;
            f.blocks[pre].stmts.extend(moved);
        }
    }
}

/// The locals that `f` assigns in one place.
fn assigned_once(f: &Function) -> HashSet<Local> {
    let mut seen = HashSet::new();
    let mut twice = HashSet::new();
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        if let Stmt::Assign(d, _) = s
            && !seen.insert(*d)
        {
            twice.insert(*d);
        }
    }
    seen.difference(&twice).copied().collect()
}
