//! Steps taken without a branch. `if c { x += k }` lowers to a branch on `c` around the step,
//! which a predictor guesses badly when `c` follows the data, as when counting the elements
//! that hold; the branch becomes the step by `c * k`, which steps by 0 where `c` is false
//! (goal debug-speed). A condition is a `bool`, so 0 or 1. The step keeps its check and its
//! location, and overflows exactly where the branch's step did, where `c` is true, so a program
//! panics where and how it did (numbers.integer-panics).
//!
//! The block around which the branch goes may copy integers and step one: each local it gives
//! a new value must hold its old value again when the step is by 0, as `x` does, or be read in
//! that block alone, as the temporaries that lowering makes are. The other way may only do what
//! the block does last, as both ways assign the `if`'s value `()`.

use std::collections::HashMap;

use crate::mir::{
    BlockId, Const, Function, Local, LocalDecl, NumKind, Operand, Prim, Repr, Rvalue, Stmt,
    Terminator,
};
use crate::opt::loops::predecessors;

/// A branch around a step: its condition, the block it goes around, the number of statements
/// that the other way runs too, which end that block, and the block where both ways meet.
struct Diamond {
    cond: Local,
    around: usize,
    shared: usize,
    join: BlockId,
}

/// Replaces each branch of `f` around a step by the step, and returns whether any changed. The
/// blocks it went around are left for pruning.
pub(crate) fn unbranch(f: &mut Function) -> bool {
    let preds = predecessors(f);
    let readers = readers(f);
    let mut changed = false;
    for b in 0..f.blocks.len() {
        let Some(d) = diamond(f, &preds, b) else {
            continue;
        };
        let Some(stmts) = stepped(f, &readers, &d) else {
            continue;
        };
        f.blocks[b].stmts.extend(stmts);
        f.blocks[b].term = Terminator::Goto(d.join);
        changed = true;
    }
    changed
}

/// Block `b`'s branch, if each way is reached from `b` alone and jumps on to the same block,
/// and the way taken when the condition doesn't hold does only what the other does last.
fn diamond(f: &Function, preds: &[Vec<usize>], b: usize) -> Option<Diamond> {
    let Terminator::Branch {
        cond: Operand::Local(cond),
        then,
        otherwise,
    } = f.blocks[b].term
    else {
        return None;
    };
    let (around, other) = (then.0 as usize, otherwise.0 as usize);
    let alone = |x: usize| x != b && preds[x] == [b];
    if around == other || !alone(around) || !alone(other) {
        return None;
    }
    let (Terminator::Goto(join), Terminator::Goto(also)) =
        (f.blocks[around].term.clone(), f.blocks[other].term.clone())
    else {
        return None;
    };
    let meets_elsewhere = ![b, around, other].contains(&(join.0 as usize));
    if join != also || !meets_elsewhere || f.locals[cond.0 as usize].slot {
        return None;
    }
    let (steps, rest) = (core(&f.blocks[around].stmts), core(&f.blocks[other].stmts));
    steps.ends_with(&rest).then_some(Diamond {
        cond,
        around,
        shared: rest.len(),
        join,
    })
}

/// A block's statements but its markers of source locations.
fn core(stmts: &[Stmt]) -> Vec<&Stmt> {
    stmts
        .iter()
        .filter(|s| !matches!(s, Stmt::At(_) | Stmt::Count(..)))
        .collect()
}

/// What each local the block assigns holds where the step is by 0: the old value of a local,
/// or a new value.
type Holds = HashMap<Local, Option<Local>>;

/// The statements of the block that the branch goes around with its step made by the
/// condition times its constant, if it steps one integer and otherwise only copies and sets
/// scalars, as the module says.
fn stepped(f: &mut Function, readers: &[Vec<usize>], d: &Diamond) -> Option<Vec<Stmt>> {
    let stmts = &f.blocks[d.around].stmts;
    let own = own_part(stmts, d.shared)?;
    let mut holds = Holds::new();
    let mut step = None;
    for (at, stmt) in stmts[..own].iter().enumerate() {
        let Stmt::Assign(dest, r) = stmt else {
            if matches!(stmt, Stmt::At(_) | Stmt::Count(..)) {
                continue;
            }
            return None;
        };
        let decl = &f.locals[dest.0 as usize];
        if *dest == d.cond || decl.slot || decl.repr != Repr::Scalar {
            return None;
        }
        let old = |l: Local| holds.get(&l).copied().unwrap_or(Some(l));
        let held = match r {
            Rvalue::Use(Operand::Local(source)) => old(*source),
            Rvalue::Use(Operand::Const(_)) => None,
            Rvalue::Prim(op, args, _) if step.is_none() => {
                let (stepped, by) = constant_step(*op, args)?;
                step = Some((at, by));
                old(stepped)
            }
            _ => return None,
        };
        holds.insert(*dest, held);
    }
    let changed: Vec<Local> = holds
        .iter()
        .filter(|&(&l, &held)| held != Some(l))
        .map(|(&l, _)| l)
        .collect();
    let read_after = stmts[own..]
        .iter()
        .any(|s| reads(s).iter().any(|l| changed.contains(l)));
    let elsewhere = changed
        .iter()
        .any(|l| readers[l.0 as usize].iter().any(|&b| b != d.around));
    if read_after || elsewhere {
        return None;
    }
    let (at, by) = step?;
    Some(by_condition(f, d, at, by))
}

/// How many statements of `stmts` come before the last `shared` that aren't markers.
fn own_part(stmts: &[Stmt], shared: usize) -> Option<usize> {
    if shared == 0 {
        return Some(stmts.len());
    }
    let mut seen = 0;
    for (at, stmt) in stmts.iter().enumerate().rev() {
        if !matches!(stmt, Stmt::At(_) | Stmt::Count(..)) {
            seen += 1;
            if seen == shared {
                return Some(at);
            }
        }
    }
    None
}

/// The statements of the block that the branch goes around, with the step at `at` made by the
/// condition times `by`.
fn by_condition(f: &mut Function, d: &Diamond, at: usize, by: i64) -> Vec<Stmt> {
    let mut stmts = f.blocks[d.around].stmts.clone();
    let (operand, at) = if by == 1 {
        (Operand::Local(d.cond), at)
    } else {
        let times = scalar(f);
        let product = Rvalue::Prim(
            Prim::MulWrap(NumKind::I64),
            vec![Operand::Local(d.cond), Operand::word(by.cast_unsigned())],
            Operand::word(0),
        );
        stmts.insert(at, Stmt::Assign(times, product));
        (Operand::Local(times), at + 1)
    };
    if let Stmt::Assign(_, Rvalue::Prim(_, args, _)) = &mut stmts[at]
        && let Some(constant) = args.iter_mut().find(|a| matches!(a, Operand::Const(_)))
    {
        *constant = operand;
    }
    stmts
}

/// The locals a statement reads.
fn reads(stmt: &Stmt) -> Vec<Local> {
    let operands: Vec<&Operand> = match stmt {
        Stmt::Assign(_, r) => r.operands(),
        Stmt::Store { slot, value, .. } => vec![slot, value],
        Stmt::Effect(_, args) => args.iter().collect(),
        Stmt::Dup(_) | Stmt::Drop(_) | Stmt::ReleaseConstants | Stmt::At(_) | Stmt::Count(..) => {
            Vec::new()
        }
    };
    let mut out: Vec<Local> = operands.into_iter().filter_map(Operand::local).collect();
    if let Stmt::Dup(l) | Stmt::Drop(l) = stmt {
        out.push(*l);
    }
    out
}

/// The local and the constant of an integer step: `x + k`, `k + x` or `x - k`.
fn constant_step(op: Prim, args: &[Operand]) -> Option<(Local, i64)> {
    let constant = |o: &Operand| match o {
        Operand::Const(Const::Word(w)) => Some(w.cast_signed()),
        _ => None,
    };
    match (op, args) {
        (Prim::Add(NumKind::I64) | Prim::Sub(NumKind::I64), [Operand::Local(x), k]) => {
            Some((*x, constant(k)?))
        }
        (Prim::Add(NumKind::I64), [k, Operand::Local(x)]) => Some((*x, constant(k)?)),
        _ => None,
    }
}

/// A new local that holds a scalar.
fn scalar(f: &mut Function) -> Local {
    let l = Local(u32::try_from(f.locals.len()).expect("under 4G locals"));
    f.locals.push(LocalDecl {
        repr: Repr::Scalar,
        slot: false,
        grouped: false,
        borrowed: false,
        var: false,
        name: None,
        shown: None,
    });
    l
}

/// The blocks that read each local of `f`.
fn readers(f: &Function) -> Vec<Vec<usize>> {
    let mut out = vec![Vec::new(); f.locals.len()];
    for (b, block) in f.blocks.iter().enumerate() {
        let term = block.term.operands().into_iter().filter_map(Operand::local);
        for l in block.stmts.iter().flat_map(reads).chain(term) {
            out[l.0 as usize].push(b);
        }
    }
    out
}
