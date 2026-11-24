//! Cheap optimizations of a function's MIR, before its reference counting and Cranelift
//! (goal debug-speed). Each reads and rewrites one function and nothing else, so an edit still
//! compiles again only the functions it changes, and each can be patched alone
//! (edit-to-running-program).
//!
//! First, a user function inlines what it calls of the standard library, and the closures
//! that this code calls ([`inline`]), which never change while the program runs: each object
//! that it then makes and only reads field by field is replaced by the words it reads
//! ([`boxes`]), and the copies left are read through ([`copies`]). Then a repeated operation
//! copies the result of the first ([`reuse`]), the branches of `&&`
//! and `||` test their condition once ([`branches`]), and `if c { x += 1 }` steps `x` by `c`,
//! without a branch ([`steps`]). Then the checks that facts local to the
//! function prove can't fail are removed ([`ranges`]): the bounds check of `xs[i]`, read or
//! written, where `i` lies in `[0, xs.len())`, as the counter of `for i in 0..xs.len()` does
//! where the loop's test has held, and the overflow check of `i + 1` where `i` is below another
//! integer, which is at most the maximum. A write in bounds still makes its list unique
//!. A check that can fail is kept, so a program panics where and how it did,
//! with the same report (numbers.integer-panics).
//!
//! Once its reference counting is inserted, a function's lists are made unique once
//! ([`unique`]): before a loop that writes one, and not again by a write that follows another
//! while nothing can have shared the list.

mod arith;
pub(crate) mod boxes;
mod branches;
mod constants;
mod copies;
mod defs;
mod facts;
pub(crate) mod inline;
mod loops;
mod onto;
mod places;
mod ranges;
mod reuse;
mod steps;
mod unique;

#[cfg(test)]
mod tests;

pub use crate::opt::defs::definitions;

use crate::FnRef;
use crate::mir::{BlockId, Function, NumKind, Operand, Prim, Runtime, Rvalue, Stmt, Terminator};
use crate::opt::arith::{add_fits, mul_fits, sub_fits};
use crate::opt::facts::{Fact, Facts, Holder, Term};
use crate::opt::ranges::{Cx, solve};

/// Optimizes a function in place. A function that met the error type can't run, so it is left
/// as it is.
pub fn optimize(f: &mut Function) {
    if !f.broken {
        reuse::reuse(f);
        constants::hoist(f);
        let threaded = branches::thread(f);
        if steps::unbranch(f) || threaded {
            crate::prune::keep_reachable(f);
        }
        if discharge(f) {
            crate::prune::keep_reachable(f);
        }
    }
}

/// Optimizes a function in place that its reference counting reads, which `stilt-rc` has
/// inserted: each list is made unique once, and a string an interpolation starts with is
/// appended to in place when nothing else references it.
pub fn optimize_counted(f: &mut Function) {
    if !f.broken {
        unique::once(f);
        onto::concatenate_onto(f);
    }
}

/// Appends to and pops from in place each list that a function's counted MIR proves unique,
/// for a release build, whose C then keeps the list's length and elements in locals across them.
/// A debug build keeps the append through the list's slot, which checks its count: Cranelift's
/// code for it runs nsieve's loop that fills its list in 17 ms, where an append in place took 22.
pub fn in_place(f: &mut Function) {
    if !f.broken {
        unique::in_place(f);
    }
}

/// Whether `f` is the standard library's `List.len`, a native whose result is a list's length.
pub(crate) fn is_list_len(f: &FnRef) -> bool {
    matches!(f, FnRef::Member(owner, name)
        if &*owner.home == "std.prelude" && &*owner.name == "List" && &**name == "len")
}

/// Whether `f` is the standard library's `List.pop`.
pub(crate) fn is_list_pop(f: &FnRef) -> bool {
    matches!(f, FnRef::Member(owner, name)
        if &*owner.home == "std.prelude" && &*owner.name == "List" && &**name == "pop")
}

/// Replaces each checked operation whose check the facts that hold before it prove can't
/// fail by the same operation unchecked: an element read or an element's slot taken in bounds,
/// an addition, a subtraction or a multiplication that can't overflow, and a division by a
/// positive divisor. An
/// addition of two integers at least 0 gets the check of one that can only overflow upward,
/// and a branch whose condition the facts decide becomes a jump, as the test that ends each
/// iteration of `for i in a..b` does, the loop's test having held. Returns whether a branch
/// became a jump, which may leave blocks that nothing reaches.
fn discharge(f: &mut Function) -> bool {
    let cx = Cx::new(f);
    let Some(ins) = solve(&cx, f) else {
        return false;
    };
    let mut jumped = false;
    for (block, facts) in f.blocks.iter_mut().zip(ins) {
        let Some(mut facts) = facts else { continue };
        for s in &mut block.stmts {
            if let Stmt::Assign(_, r) = s
                && let Some(unchecked) = discharged(&cx, &facts, r)
            {
                *r = unchecked;
            }
            cx.stmt(&mut facts, s);
        }
        if let Some(to) = decided(&facts, &block.term) {
            block.term = Terminator::Goto(to);
            jumped = true;
        }
    }
    jumped
}

/// Where a branch goes, if the facts decide its condition.
fn decided(facts: &Facts, t: &Terminator) -> Option<BlockId> {
    let Terminator::Branch {
        cond: Operand::Local(c),
        then,
        otherwise,
    } = *t
    else {
        return None;
    };
    facts.iter().find_map(|f| match f {
        Fact::Cond(l, rel) if l == c => {
            if facts.holds(rel) {
                Some(then)
            } else if facts.holds(rel.negated()) {
                Some(otherwise)
            } else {
                None
            }
        }
        _ => None,
    })
}

/// `r` without its check, if `facts` prove that the check can't fail.
fn discharged(cx: &Cx, facts: &Facts, r: &Rvalue) -> Option<Rvalue> {
    match r {
        Rvalue::Runtime(Runtime::ListIndex, args) => {
            // `(loc, list, i, elem, word)`, and unchecked, the same without `loc`.
            let [_, Operand::Local(list), i, ..] = args.as_slice() else {
                return None;
            };
            let index = cx.term(i)?;
            let inside = facts
                .holders(*list)
                .into_iter()
                .any(|h| facts.in_bounds(index, h));
            inside.then(|| Rvalue::Runtime(Runtime::ListAt, args[1..].to_vec()))
        }
        Rvalue::Runtime(Runtime::ListSlot, args) => {
            // `(loc, slot, i, elem)`, and unchecked, the same without `loc`. The list is the one
            // the slot's place holds, never one an element holds, which no fact names.
            let [_, slot, i, _] = args.as_slice() else {
                return None;
            };
            let (place, index) = (cx.place_of(slot)?, cx.term(i)?);
            facts
                .in_bounds(index, Holder::Place(place))
                .then(|| Rvalue::Runtime(Runtime::ListSlotAt, args[1..].to_vec()))
        }
        Rvalue::Prim(Prim::Add(NumKind::I64), args, loc) => {
            let (a, b) = operands(cx, args)?;
            let op = if add_fits(facts, a, b) {
                Prim::AddWrap(NumKind::I64)
            } else if facts.nonneg(a) && facts.nonneg(b) {
                Prim::AddUp(NumKind::I64)
            } else {
                return None;
            };
            Some(Rvalue::Prim(op, args.clone(), loc.clone()))
        }
        Rvalue::Prim(Prim::Sub(NumKind::I64), args, loc) => {
            let (a, b) = operands(cx, args)?;
            sub_fits(facts, a, b)
                .then(|| Rvalue::Prim(Prim::SubWrap(NumKind::I64), args.clone(), loc.clone()))
        }
        Rvalue::Prim(Prim::Mul(NumKind::I64), args, loc) => {
            let (a, b) = operands(cx, args)?;
            mul_fits(facts, a, b)
                .then(|| Rvalue::Prim(Prim::MulWrap(NumKind::I64), args.clone(), loc.clone()))
        }
        Rvalue::Prim(op @ (Prim::Div(NumKind::I64) | Prim::Rem(NumKind::I64)), args, loc) => {
            // A positive divisor is neither 0 nor -1, by which a division panics.
            let (_, b) = operands(cx, args)?;
            let unchecked = if matches!(op, Prim::Div(_)) {
                Prim::DivByPositive(NumKind::I64)
            } else {
                Prim::RemByPositive(NumKind::I64)
            };
            facts
                .lt(Term::Const(0), b)
                .then(|| Rvalue::Prim(unchecked, args.clone(), loc.clone()))
        }
        _ => None,
    }
}

/// The two operands of a binary operation, as terms.
fn operands(cx: &Cx, args: &[Operand]) -> Option<(Term, Term)> {
    match args {
        [a, b] => Some((cx.term(a)?, cx.term(b)?)),
        _ => None,
    }
}
