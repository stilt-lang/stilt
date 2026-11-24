//! Branches threaded through what a block already knows. `a && b` and `a || b` lower to a
//! block that only branches on the condition's local, which each way in assigns: a jump to it
//! branches there instead, and a branch whose outcome fixes the local goes straight to where it
//! leads, so the condition is tested once. A branch on `!c` branches on `c` the other way, so
//! Cranelift fuses the comparison that computes `c` with the branch.
//!
//! Every loop keeps a jump back that polls the stop flag of a watched run: only a jump forward
//! is replaced, so each cycle keeps every jump back it had.

use crate::mir::{
    Block, BlockId, Function, Local, LocalDecl, Operand, Prim, Rvalue, Stmt, Terminator,
};

/// Threads the branches of `f`, and returns whether any changed.
pub(crate) fn thread(f: &mut Function) -> bool {
    let mut changed = false;
    for p in 0..f.blocks.len() {
        changed |= duplicate(f, p);
        changed |= shortcut(f, p);
        negate(&mut f.blocks[p], &f.locals);
    }
    changed
}

/// The branch of a block that does nothing else, and so can be taken from wherever it is
/// reached: its condition, and where each outcome leads.
fn lone_branch(block: &Block) -> Option<(Local, BlockId, BlockId)> {
    if !block
        .stmts
        .iter()
        .all(|s| matches!(s, Stmt::At(_) | Stmt::Count(..)))
    {
        return None;
    }
    match block.term {
        Terminator::Branch {
            cond: Operand::Local(c),
            then,
            otherwise,
        } => Some((c, then, otherwise)),
        _ => None,
    }
}

/// Replaces block `p`'s jump forward to a lone branch by that branch.
fn duplicate(f: &mut Function, p: usize) -> bool {
    let Terminator::Goto(b) = f.blocks[p].term else {
        return false;
    };
    let Some((c, then, otherwise)) = lone_branch(&f.blocks[b.0 as usize]) else {
        return false;
    };
    if (b.0 as usize) <= p || then == b || otherwise == b {
        return false;
    }
    f.blocks[p].term = Terminator::Branch {
        cond: Operand::Local(c),
        then,
        otherwise,
    };
    true
}

/// Sends each edge of block `p`'s branch on `x` that reaches a lone branch on `c`, where `c`
/// holds `x`, to where the lone branch leads on the same outcome.
fn shortcut(f: &mut Function, p: usize) -> bool {
    let Terminator::Branch {
        cond: Operand::Local(x),
        then,
        otherwise,
    } = f.blocks[p].term
    else {
        return false;
    };
    let mut changed = false;
    let mut outcome = |to: BlockId, taken: bool| -> BlockId {
        let Some((c, yes, no)) = lone_branch(&f.blocks[to.0 as usize]) else {
            return to;
        };
        if c != x && !copies(&f.blocks[p], &f.locals, c, x) {
            return to;
        }
        changed = true;
        if taken { yes } else { no }
    };
    let (then, otherwise) = (outcome(then, true), outcome(otherwise, false));
    f.blocks[p].term = Terminator::Branch {
        cond: Operand::Local(x),
        then,
        otherwise,
    };
    changed
}

/// Whether `c` holds the value of `x` at the end of the block: its last assignment there
/// copies `x`, which nothing after it changes, and neither lives in memory, where a pointer can
/// change it.
fn copies(block: &Block, locals: &[LocalDecl], c: Local, x: Local) -> bool {
    if locals[c.0 as usize].slot || locals[x.0 as usize].slot {
        return false;
    }
    for s in block.stmts.iter().rev() {
        match s {
            Stmt::Assign(d, Rvalue::Use(Operand::Local(s))) if *d == c => return *s == x,
            Stmt::Assign(d, _) if *d == c || *d == x => return false,
            _ => {}
        }
    }
    false
}

/// Turns a branch on `!n`, which the block computes, maybe through copies, into one on `n`
/// with its outcomes swapped, when nothing after it changes `n`. Locals that live in memory are
/// left alone, since a pointer can change them.
fn negate(block: &mut Block, locals: &[LocalDecl]) {
    let Terminator::Branch {
        cond: Operand::Local(mut c),
        then,
        otherwise,
    } = block.term
    else {
        return;
    };
    let in_memory = |l: &Local| locals[l.0 as usize].slot;
    if in_memory(&c) {
        return;
    }
    // The locals that the statements after the one being read assign.
    let mut later: Vec<Local> = Vec::new();
    for s in block.stmts.iter().rev() {
        let Stmt::Assign(d, r) = s else { continue };
        if *d == c {
            match r {
                Rvalue::Use(Operand::Local(s)) if !later.contains(s) && !in_memory(s) => {
                    c = *s;
                }
                Rvalue::Prim(Prim::BoolNot, args, _) => {
                    if let [Operand::Local(n)] = args.as_slice()
                        && !later.contains(n)
                        && !in_memory(n)
                    {
                        block.term = Terminator::Branch {
                            cond: Operand::Local(*n),
                            then: otherwise,
                            otherwise: then,
                        };
                    }
                    return;
                }
                _ => return,
            }
        }
        later.push(*d);
    }
}
