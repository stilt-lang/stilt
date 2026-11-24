//! Appending to and popping from a list where it is, for a release build: each append to and
//! each pop from a list that the facts prove unique checks nothing of the list's count, so that
//! the C keeps the list's length and elements in locals across them.

use super::{Cx, fresh_local, solve};
use crate::mir::{
    Arg, Callee, Const, Function, Operand, Runtime, Rvalue, Stmt, Terminator, UNIQUE_LIST,
};

/// Replaces each append to a list that the facts prove unique by an append to the list where
/// it is, and marks the location of each pop from one ([`UNIQUE_LIST`]).
pub(crate) fn in_place(f: &mut Function) {
    let cx = Cx::new(f);
    let ins = solve(&cx, f);
    let mut appends = Vec::new();
    let mut pops = Vec::new();
    for (b, (block, u)) in f.blocks.iter().zip(ins).enumerate() {
        let Some(mut u) = u else { continue };
        for (at, s) in block.stmts.iter().enumerate() {
            if let Stmt::Effect(Runtime::ListAppend, args) = s
                && cx.known(&u, &args[0])
            {
                appends.push((b, at));
            }
            cx.stmt(&mut u, s);
        }
        if let Some(slot) = popped(&block.term)
            && cx.known(&u, slot)
        {
            pops.push(b);
        }
    }
    for (b, at) in appends.into_iter().rev() {
        append_in_place(f, b, at);
    }
    for b in pops {
        if let Terminator::Call { args, .. } = &mut f.blocks[b].term
            && let Some(Arg::Borrow(Operand::Const(Const::Word(loc)))) = args.first_mut()
        {
            *loc |= UNIQUE_LIST;
        }
    }
}

/// The pointer to the slot whose list a call of the standard library's `List.pop` pops.
fn popped(t: &Terminator) -> Option<&Operand> {
    match t {
        Terminator::Call {
            callee: Callee::Direct(f),
            args,
            ..
        } if crate::opt::is_list_pop(f) => args.iter().find_map(|a| match a {
            Arg::Ref(slot) => Some(slot),
            _ => None,
        }),
        _ => None,
    }
}

/// Replaces the append at statement `at` of block `b`, to the list a place holds, which is
/// unique, by an append to that list where it is: it stays the place's, since growing a list
/// moves its elements, never the list.
fn append_in_place(f: &mut Function, b: usize, at: usize) {
    let Stmt::Effect(Runtime::ListAppend, args) = &f.blocks[b].stmts[at] else {
        return;
    };
    let mut args = args.clone();
    let list = fresh_local(f);
    let slot = std::mem::replace(&mut args[0], Operand::Local(list));
    let stmts = &mut f.blocks[b].stmts;
    stmts[at] = Stmt::Effect(Runtime::ListPush, args);
    stmts.insert(at, Stmt::Assign(list, Rvalue::Load(slot)));
}
