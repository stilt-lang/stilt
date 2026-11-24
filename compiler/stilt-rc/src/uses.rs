//! What each statement and terminator does to the locals it names: which it reads, which it
//! consumes, and which it defines (`stilt_mir::mir` states the rules).

use stilt_mir::mir::{Arg, Callee, Local, Operand, Rvalue, Stmt, Terminator};

/// How a statement names a local.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Use {
    /// Read for the statement, and kept by its owner.
    Borrow,
    /// Given away: the statement takes the reference.
    Consume,
}

fn operand(o: &Operand, how: Use, out: &mut Vec<(Local, Use)>) {
    if let Operand::Local(l) = o {
        out.push((*l, how));
    }
}

/// A local a statement defines, and whether it gets a reference of its own.
pub(crate) type Def = (Local, bool);

/// The locals an rvalue names, and whether the local it defines gets a reference of its own.
pub(crate) fn rvalue_uses(r: &Rvalue, out: &mut Vec<(Local, Use)>) -> bool {
    match r {
        Rvalue::Use(o) => {
            operand(o, Use::Consume, out);
            true
        }
        Rvalue::Prim(_, args, loc) => {
            for a in args {
                operand(a, Use::Borrow, out);
            }
            operand(loc, Use::Borrow, out);
            true
        }
        Rvalue::Alloc(_, fields) => {
            for (f, _) in fields {
                operand(f, Use::Consume, out);
            }
            true
        }
        Rvalue::AllocIn(memory, _, fields, _) => {
            operand(memory, Use::Borrow, out);
            for (f, _) in fields {
                operand(f, Use::Consume, out);
            }
            true
        }
        Rvalue::Field { base, .. } => {
            operand(base, Use::Borrow, out);
            false
        }
        Rvalue::Tag(o) | Rvalue::Offset(o, _) => {
            operand(o, Use::Borrow, out);
            true
        }
        Rvalue::Load(o) => {
            operand(o, Use::Borrow, out);
            false
        }
        Rvalue::SlotOf(_) => true,
        Rvalue::FieldSlot { slot, .. } => {
            operand(slot, Use::Borrow, out);
            true
        }
        Rvalue::Runtime(f, args) => {
            for (i, a) in args.iter().enumerate() {
                let how = if f.consumes(i) {
                    Use::Consume
                } else {
                    Use::Borrow
                };
                operand(a, how, out);
            }
            !f.borrows()
        }
        Rvalue::Constant(_, loc, ..) => {
            operand(loc, Use::Borrow, out);
            false
        }
    }
}

/// The locals a statement names, the local it defines, and whether that local gets a
/// reference of its own.
pub(crate) fn stmt_uses(s: &Stmt) -> (Vec<(Local, Use)>, Option<Def>) {
    let mut out = Vec::new();
    let def = match s {
        Stmt::Assign(dest, r) => Some((*dest, rvalue_uses(r, &mut out))),
        Stmt::Store { slot, value, .. } => {
            operand(slot, Use::Borrow, &mut out);
            operand(value, Use::Consume, &mut out);
            None
        }
        Stmt::Effect(f, args) => {
            for (i, a) in args.iter().enumerate() {
                let how = if f.consumes(i) {
                    Use::Consume
                } else {
                    Use::Borrow
                };
                operand(a, how, &mut out);
            }
            None
        }
        Stmt::ReleaseConstants | Stmt::Dup(_) | Stmt::Drop(_) | Stmt::At(_) | Stmt::Count(..) => {
            None
        }
    };
    (out, def)
}

/// The locals a terminator names.
pub(crate) fn term_uses(t: &Terminator) -> Vec<(Local, Use)> {
    let mut out = Vec::new();
    match t {
        Terminator::Branch { cond, .. } => operand(cond, Use::Borrow, &mut out),
        Terminator::Switch { value, .. } => operand(value, Use::Borrow, &mut out),
        Terminator::Call { callee, args, .. } => {
            match callee {
                Callee::Direct(_) => {}
                Callee::Value(o) | Callee::Method(o, _) => operand(o, Use::Borrow, &mut out),
            }
            for a in args {
                match a {
                    Arg::Borrow(o) | Arg::Ref(o) => operand(o, Use::Borrow, &mut out),
                    Arg::Own(o) => operand(o, Use::Consume, &mut out),
                    Arg::Lend(words) => {
                        for (o, _) in words {
                            operand(o, Use::Borrow, &mut out);
                        }
                    }
                }
            }
        }
        Terminator::Return(os) | Terminator::Raise(os) => {
            for o in os {
                operand(o, Use::Consume, &mut out);
            }
        }
        Terminator::Panic { detail, loc, .. } => {
            if let Some(d) = detail {
                operand(d, Use::Borrow, &mut out);
            }
            operand(loc, Use::Borrow, &mut out);
        }
        Terminator::Goto(_) | Terminator::Unreachable => {}
    }
    out
}

/// The locals a terminator defines on its way to a successor: the words of a call's result,
/// or of its error.
pub(crate) fn edge_def(t: &Terminator, to: stilt_mir::mir::BlockId) -> &[Local] {
    match t {
        Terminator::Call {
            dest, next, raised, ..
        } => {
            if let Some((error, block)) = raised
                && *block == to
                && *next != to
            {
                error
            } else {
                dest
            }
        }
        _ => &[],
    }
}
