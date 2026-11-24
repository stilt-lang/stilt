//! Moving the counting of a value's fields to the release of the value, so that a release that
//! keeps the value's memory hands its fields over instead (Perceus's drop specialization).
//!
//! A local read from a field of another, its parent, is counted where it is read when it lives
//! past its block, and released after its last use, which may come before the parent's release.
//! A release of such a local moves to where the parent's is, when a block that the branch goes to
//! starts with it; a copy moves forward past what only reads, into the blocks a branch goes to,
//! and meets either a release of the same local, and both go, or the parent's release, which
//! takes it over ([`fuse`]): the parent's memory kept, the field's reference is the parent's,
//! and the copy is made only when the memory isn't kept.

use stilt_mir::mir::{Function, Local, Operand, Runtime, Rvalue, Stmt, Terminator};

/// The local each local is a field of, and the field's index, for each local of one word that
/// one statement defines from a field of a local that lives outside memory, is defined once and
/// keeps its value alive: a parameter, or a local with a reference of its own, which a release
/// shows.
pub(super) fn fields_of(f: &Function) -> Vec<Option<(Local, u32)>> {
    let defs = stilt_mir::opt::definitions(f);
    let mut keeps = vec![false; f.locals.len()];
    for p in &f.params {
        keeps[p.local.0 as usize] = true;
    }
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        if let Stmt::Drop(x) = s {
            keeps[x.0 as usize] = true;
        }
    }
    let mut out = vec![None; f.locals.len()];
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        if let Stmt::Assign(
            y,
            Rvalue::Field {
                base: Operand::Local(x),
                index,
                ..
            },
        ) = s
            && defs[y.0 as usize] == 1
            && f.locals[y.0 as usize].repr.words() == 1
            && defs[x.0 as usize] == 1
            && keeps[x.0 as usize]
            && !f.locals[x.0 as usize].slot
        {
            out[y.0 as usize] = Some((*x, *index));
        }
    }
    out
}

/// The number of edges into each block.
fn predecessors(f: &Function) -> Vec<usize> {
    let mut preds = vec![0; f.blocks.len()];
    for b in &f.blocks {
        for s in b.term.successors() {
            preds[s.0 as usize] += 1;
        }
    }
    preds
}

/// The blocks that block `b` goes to, if it ends in a branch to blocks that nothing else goes
/// to, so that what follows its statements is the start of each.
fn only_successors(f: &Function, b: usize, preds: &[usize]) -> Option<Vec<usize>> {
    let term = &f.blocks[b].term;
    if !matches!(
        term,
        Terminator::Goto(_) | Terminator::Branch { .. } | Terminator::Switch { .. }
    ) {
        return None;
    }
    let succs: Vec<usize> = term.successors().iter().map(|s| s.0 as usize).collect();
    succs
        .iter()
        .all(|&s| s != b && preds[s] == 1)
        .then_some(succs)
}

/// Whether block `s` starts by releasing `x`, among the releases that its edge put first.
fn starts_releasing(f: &Function, s: usize, x: Local) -> bool {
    f.blocks[s]
        .stmts
        .iter()
        .take_while(|st| matches!(st, Stmt::Drop(_)))
        .any(|st| *st == Stmt::Drop(x))
}

/// Moves each release of a field to the blocks a branch goes to, when one of them starts by
/// releasing its parent: after that release there, and first thing in the others.
pub(super) fn sink_drops(f: &mut Function, fields: &[Option<(Local, u32)>]) {
    let preds = predecessors(f);
    for b in 0..f.blocks.len() {
        let Some(succs) = only_successors(f, b, &preds) else {
            continue;
        };
        let moving: Vec<(usize, Local, Local)> = (f.blocks[b].stmts.iter().enumerate())
            .filter_map(|(i, s)| match s {
                Stmt::Drop(y) => fields[y.0 as usize].map(|(x, _)| (i, *y, x)),
                _ => None,
            })
            .filter(|&(_, _, x)| succs.iter().any(|&s| starts_releasing(f, s, x)))
            .collect();
        for &(i, y, x) in moving.iter().rev() {
            f.blocks[b].stmts.remove(i);
            for &s in &succs {
                let stmts = &mut f.blocks[s].stmts;
                let at = stmts
                    .iter()
                    .position(|st| *st == Stmt::Drop(x))
                    .filter(|&p| stmts[..p].iter().all(|st| matches!(st, Stmt::Drop(_))))
                    .map_or(0, |p| p + 1);
                stmts.insert(at, Stmt::Drop(y));
            }
        }
    }
}

/// Whether a copy of `field`, read from `whole`, may move past `stmt`: `stmt` only reads them,
/// if it names them, and releases nothing but another local.
fn passable(stmt: &Stmt, field: Local, whole: Local) -> bool {
    let named = |o: &Operand| *o == Operand::Local(field) || *o == Operand::Local(whole);
    match stmt {
        Stmt::At(_) | Stmt::Count(..) | Stmt::Dup(_) => true,
        Stmt::Drop(other) => *other != whole && *other != field,
        Stmt::Assign(dest, rvalue) => {
            *dest != whole
                && *dest != field
                && match rvalue {
                    Rvalue::Field { .. } | Rvalue::Tag(_) | Rvalue::Prim(..) => true,
                    Rvalue::Use(o) => !named(o),
                    _ => false,
                }
        }
        _ => false,
    }
}

/// Moves each copy of a field forward past what only reads it, into the blocks a branch goes
/// to, until it meets what it can't move past: a release of the same local, and both go, or
/// any other statement, before which it stays.
pub(super) fn sink_dups(f: &mut Function, fields: &[Option<(Local, u32)>]) {
    let preds = predecessors(f);
    let mut budget = 4 * f.blocks.iter().map(|b| b.stmts.len() + 1).sum::<usize>();
    let mut todo: Vec<usize> = (0..f.blocks.len()).rev().collect();
    while let Some(b) = todo.pop() {
        let mut i = 0;
        while i < f.blocks[b].stmts.len() && budget > 0 {
            budget -= 1;
            let Stmt::Dup(y) = f.blocks[b].stmts[i] else {
                i += 1;
                continue;
            };
            let Some((x, _)) = fields[y.0 as usize] else {
                i += 1;
                continue;
            };
            i = sink_one(f, (b, i), (y, x), &preds, &mut todo);
        }
    }
}

/// Moves the copy of `field`, read from `whole`, at statement `at` of block `block`, and gives
/// the index of the statement to look at next there.
fn sink_one(
    f: &mut Function,
    (block, at): (usize, usize),
    (field, whole): (Local, Local),
    preds: &[usize],
    todo: &mut Vec<usize>,
) -> usize {
    let stmts = &f.blocks[block].stmts;
    let mut j = at + 1;
    while j < stmts.len() && stmts[j] != Stmt::Drop(field) && passable(&stmts[j], field, whole) {
        j += 1;
    }
    if j < stmts.len() && stmts[j] == Stmt::Drop(field) {
        f.blocks[block].stmts.remove(j);
        f.blocks[block].stmts.remove(at);
        return at;
    }
    if j == stmts.len()
        && let Some(succs) = only_successors(f, block, preds)
    {
        f.blocks[block].stmts.remove(at);
        for s in succs {
            f.blocks[s].stmts.insert(0, Stmt::Dup(field));
            todo.push(s);
        }
        return at;
    }
    let dup = f.blocks[block].stmts.remove(at);
    f.blocks[block].stmts.insert(j - 1, dup);
    j
}

/// Folds into each release that keeps memory the copies just before it of the fields of the
/// value it releases, which the release then hands over ([`Runtime::Reclaim`]'s `taken`).
pub(super) fn fuse(f: &mut Function, fields: &[Option<(Local, u32)>]) {
    for block in &mut f.blocks {
        let mut r = 0;
        while r < block.stmts.len() {
            let Stmt::Assign(_, Rvalue::Runtime(Runtime::Reclaim, args)) = &block.stmts[r] else {
                r += 1;
                continue;
            };
            let Some(Operand::Local(x)) = args.first() else {
                r += 1;
                continue;
            };
            let x = *x;
            let mut taken = 0u64;
            let mut released: Vec<Local> = Vec::new();
            let mut i = r;
            while i > 0 && fusible(&block.stmts[i - 1], x) {
                i -= 1;
                if let Some(z) = release_of(&block.stmts[i]) {
                    released.push(z);
                }
                if let Stmt::Dup(y) = block.stmts[i]
                    && let Some((parent, index)) = fields[y.0 as usize]
                    && parent == x
                    && index < 64
                    && taken & 1 << index == 0
                    && !released.contains(&y)
                {
                    taken |= 1 << index;
                    block.stmts.remove(i);
                    r -= 1;
                }
            }
            if let Stmt::Assign(_, Rvalue::Runtime(Runtime::Reclaim, args)) = &mut block.stmts[r] {
                args[2] = Operand::word(taken);
            }
            r += 1;
        }
    }
}

/// The local a statement releases, if it releases one.
fn release_of(s: &Stmt) -> Option<Local> {
    match s {
        Stmt::Drop(z) => Some(*z),
        Stmt::Assign(_, Rvalue::Runtime(Runtime::Reclaim, args)) => args.first()?.local(),
        _ => None,
    }
}

/// Whether the search for copies to fold into a release of `x` goes on past `s`: a copy, a
/// release of another local, or a marker. A copy of a local released between it and the release
/// of `x` stays.
fn fusible(s: &Stmt, x: Local) -> bool {
    match s {
        Stmt::Dup(_) | Stmt::At(_) | Stmt::Count(..) => true,
        Stmt::Drop(z) => *z != x,
        Stmt::Assign(_, Rvalue::Runtime(Runtime::Reclaim, args)) => {
            args.first() != Some(&Operand::Local(x))
        }
        _ => false,
    }
}
