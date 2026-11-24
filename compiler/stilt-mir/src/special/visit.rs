//! Reaching every operand, representation and heapness of a function in place.

use crate::mir::{Arg, Callee, Heapness, Operand, Repr, Rvalue, Stmt, Terminator};

/// Calls `f` on each operand that a statement reads.
pub(crate) fn stmt_operands(s: &mut Stmt, f: &mut impl FnMut(&mut Operand)) {
    match s {
        Stmt::Assign(_, r) => rvalue_operands(r, f),
        Stmt::Store { slot, value, .. } => {
            f(slot);
            f(value);
        }
        Stmt::Effect(_, args) => args.iter_mut().for_each(f),
        Stmt::ReleaseConstants | Stmt::Dup(_) | Stmt::Drop(_) | Stmt::At(_) | Stmt::Count(..) => {}
    }
}

/// Calls `f` on each operand that an rvalue reads.
pub(crate) fn rvalue_operands(r: &mut Rvalue, f: &mut impl FnMut(&mut Operand)) {
    match r {
        Rvalue::Use(o)
        | Rvalue::Tag(o)
        | Rvalue::Load(o)
        | Rvalue::Constant(_, o, ..)
        | Rvalue::Offset(o, _)
        | Rvalue::Field { base: o, .. }
        | Rvalue::FieldSlot { slot: o, .. } => f(o),
        Rvalue::Prim(_, args, loc) => {
            args.iter_mut().for_each(&mut *f);
            f(loc);
        }
        Rvalue::Runtime(_, args) => args.iter_mut().for_each(f),
        Rvalue::Alloc(_, fields) => fields.iter_mut().for_each(|(o, _)| f(o)),
        Rvalue::AllocIn(memory, _, fields, _) => {
            f(memory);
            for (o, _) in fields {
                f(o);
            }
        }
        Rvalue::SlotOf(_) => {}
    }
}

/// Calls `f` on each operand that a terminator reads.
pub(crate) fn term_operands(t: &mut Terminator, f: &mut impl FnMut(&mut Operand)) {
    match t {
        Terminator::Branch { cond: o, .. } | Terminator::Switch { value: o, .. } => f(o),
        Terminator::Call { callee, args, .. } => {
            if let Callee::Value(o) | Callee::Method(o, _) = callee {
                f(o);
            }
            for a in args {
                match a {
                    Arg::Borrow(o) | Arg::Own(o) | Arg::Ref(o) => f(o),
                    Arg::Lend(words) => words.iter_mut().for_each(|(o, _)| f(o)),
                }
            }
        }
        Terminator::Return(os) | Terminator::Raise(os) => os.iter_mut().for_each(f),
        Terminator::Panic { detail, loc, .. } => {
            if let Some(d) = detail {
                f(d);
            }
            f(loc);
        }
        Terminator::Goto(_) | Terminator::Unreachable => {}
    }
}

/// Replaces each heapness that a statement holds by what `f` gives.
pub(crate) fn stmt_heapnesses(s: &mut Stmt, f: &impl Fn(Heapness) -> Heapness) {
    if let Stmt::Assign(_, Rvalue::Alloc(_, fields) | Rvalue::AllocIn(_, _, fields, _)) = s {
        for (_, h) in fields {
            *h = f(*h);
        }
    }
}

/// Replaces each heapness that a terminator holds by what `f` gives.
pub(crate) fn term_heapnesses(t: &mut Terminator, f: &impl Fn(Heapness) -> Heapness) {
    if let Terminator::Call { args, .. } = t {
        for a in args {
            if let Arg::Lend(words) = a {
                for (_, h) in words {
                    *h = f(*h);
                }
            }
        }
    }
}

/// Calls `f` on each representation that a statement holds.
pub(crate) fn stmt_reprs(s: &mut Stmt, f: &impl Fn(Repr) -> Repr) {
    match s {
        Stmt::Store { repr, .. } => *repr = f(*repr),
        Stmt::Assign(_, Rvalue::Constant(_, _, _, words, _))
            if words.iter().any(|r| f(*r) != *r) =>
        {
            *words = words.iter().map(|r| f(*r)).collect();
        }
        _ => {}
    }
}
