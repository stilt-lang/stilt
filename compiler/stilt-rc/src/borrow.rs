//! Borrow inference: a local that only reads what another value holds borrows it instead of
//! owning it, so that it is neither copied when it is defined nor released after its last use,
//! as Perceus borrows (goal debug-speed: cheap debug optimizations).
//!
//! A local qualifies when it is defined once, by a read that borrows: a copy of a counted
//! local, a field of a value, a word loaded from a slot, or an element of a list or a map; when
//! every use of it is in the block that defines it, a statement or the terminator that ends the
//! block; and when nothing between its definition and its last use could release or change what
//! it reads. That excludes every store and every runtime function that writes, any new value for
//! what it reads from, and a terminator that could write: one that returns or raises, which
//! releases the slots, and a call that takes a pointer, for an `inout` argument, which is the only
//! way a callee can reach the caller's locals, since closures capture by copy
//! (expressions.capture). So `xs.len()` on an `inout` list borrows it, unless the same call takes a
//! pointer. What it reads from must in turn outlive its last use: a parameter or a slot does, an
//! owned local does if it is used again after it or is live out of the block, and a local that
//! itself borrows does if what it borrows from does.

use stilt_mir::mir::{Arg, Block, Function, Local, Operand, Runtime, Rvalue, Stmt, Terminator};

use crate::liveness::{Kinds, LocalKind, Set};
use crate::uses::{Use, stmt_uses, term_uses};

/// Where a local is used: in which block, and at which statement, or `None` for the block's
/// terminator.
type Site = (usize, Option<usize>);

/// The owned locals that can borrow their value, `live_out` being the owned locals live after
/// each block.
pub(crate) fn inferred(f: &Function, kinds: &Kinds, live_out: &[Set]) -> Vec<Local> {
    let (defs, sites) = census(f);
    let mut borrowed: Vec<Option<(usize, usize)>> = vec![None; f.locals.len()];
    let mut out = Vec::new();
    for (b, block) in f.blocks.iter().enumerate() {
        for (i, stmt) in block.stmts.iter().enumerate() {
            let Stmt::Assign(d, r) = stmt else { continue };
            if kinds.kind(*d) != LocalKind::Owned || defs[d.0 as usize] != 1 {
                continue;
            }
            let Some(sources) = sources(r) else { continue };
            let Some(last) = last_use(*d, &sites[d.0 as usize], block, b, i) else {
                continue;
            };
            let cx = Span {
                block,
                b,
                kinds,
                live_out,
                sites: &sites,
                borrowed: &borrowed,
            };
            if cx.quiet(i, last) && sources.iter().all(|&s| cx.outlives(s, i, last)) {
                borrowed[d.0 as usize] = Some((i, last));
                out.push(*d);
            }
        }
    }
    out
}

/// How many times each local is defined, and where each is used.
fn census(f: &Function) -> (Vec<usize>, Vec<Vec<Site>>) {
    let mut defs = vec![0; f.locals.len()];
    let mut sites = vec![Vec::new(); f.locals.len()];
    for p in &f.params {
        defs[p.local.0 as usize] += 1;
    }
    for (b, block) in f.blocks.iter().enumerate() {
        for (i, stmt) in block.stmts.iter().enumerate() {
            let (uses, def) = stmt_uses(stmt);
            for (l, _) in uses {
                sites[l.0 as usize].push((b, Some(i)));
            }
            if let Some((d, _)) = def {
                defs[d.0 as usize] += 1;
            }
        }
        for (l, _) in term_uses(&block.term) {
            sites[l.0 as usize].push((b, None));
        }
        for d in term_defs(&block.term) {
            defs[d.0 as usize] += 1;
        }
    }
    (defs, sites)
}

/// The locals a terminator defines: the words of a call's result and of its error.
fn term_defs(t: &Terminator) -> impl Iterator<Item = &Local> {
    let (dest, raised) = match t {
        Terminator::Call { dest, raised, .. } => (dest.as_slice(), raised.as_ref()),
        _ => (&[][..], None),
    };
    dest.iter().chain(raised.into_iter().flat_map(|(e, _)| e))
}

/// The locals a read borrows from, if `r` is a read that borrows.
pub(crate) fn sources(r: &Rvalue) -> Option<Vec<Local>> {
    let locals = |ops: &[Operand]| ops.iter().filter_map(Operand::local).collect();
    match r {
        Rvalue::Use(Operand::Local(s)) => Some(vec![*s]),
        Rvalue::Field { base, .. } => Some(locals(std::slice::from_ref(base))),
        Rvalue::Load(slot) => Some(locals(std::slice::from_ref(slot))),
        Rvalue::Runtime(f, args) if f.borrows() => Some(locals(args)),
        _ => None,
    }
}

/// The last use, in block `b`, of the local `d` defined at its statement `def`, if every use of
/// `d` is a later statement of that block or its terminator, which only borrows `d`. The
/// terminator counts as the statement after the last, and a local never used ends where it is
/// defined.
fn last_use(d: Local, sites: &[Site], block: &Block, b: usize, def: usize) -> Option<usize> {
    let mut last = Some(def);
    for &(at_block, at) in sites {
        if at_block != b {
            return None;
        }
        match at {
            Some(i) if i > def => last = last.max(Some(i)),
            None if borrows_only(&block.term, d) => last = Some(block.stmts.len()),
            Some(_) | None => return None,
        }
    }
    last
}

/// Whether a terminator names `l` only to borrow it.
fn borrows_only(t: &Terminator, l: Local) -> bool {
    term_uses(t)
        .iter()
        .all(|&(m, how)| m != l || how == Use::Borrow)
}

/// A stretch of one block's statements, and what tells whether a value lasts through it. A
/// position equal to the number of statements is the block's terminator.
struct Span<'a> {
    block: &'a Block,
    b: usize,
    kinds: &'a Kinds,
    live_out: &'a [Set],
    sites: &'a [Vec<Site>],
    /// The statements from the definition to the last use of each local found to borrow.
    borrowed: &'a [Option<(usize, usize)>],
}

impl Span<'_> {
    /// The statements after `from` up to `to`, the terminator excluded.
    fn between(&self, from: usize, to: usize) -> &[Stmt] {
        &self.block.stmts[from + 1..(to + 1).min(self.block.stmts.len())]
    }

    /// Whether the terminator is reached at `to`.
    fn reaches_term(&self, to: usize) -> bool {
        to == self.block.stmts.len()
    }

    /// Whether nothing after `from` up to `to` writes memory: a new value for a local that
    /// lives in memory releases what its slot held.
    fn quiet(&self, from: usize, to: usize) -> bool {
        let stmts = self.between(from, to).iter().all(|s| match s {
            Stmt::Assign(d, _) if self.kinds.kind(*d) == LocalKind::Slot => false,
            Stmt::Store { .. }
            | Stmt::Effect(..)
            | Stmt::ReleaseConstants
            | Stmt::Assign(_, Rvalue::FieldSlot { .. }) => false,
            Stmt::Assign(_, Rvalue::Runtime(f, _)) => !writes(*f),
            Stmt::Assign(..) | Stmt::Dup(_) | Stmt::Drop(_) | Stmt::At(_) | Stmt::Count(..) => true,
        });
        stmts && (!self.reaches_term(to) || term_quiet(&self.block.term))
    }

    /// Whether `s`, read at statement `from`, keeps its value until after statement `to`.
    fn outlives(&self, s: Local, from: usize, to: usize) -> bool {
        if self.assigned(s, from, to) {
            return false;
        }
        // A local that borrows lasts while what it borrows from lasts, which its own
        // definition read.
        if let Some((def, _)) = self.borrowed[s.0 as usize] {
            return self.reads_last(def, to);
        }
        match self.kinds.kind(s) {
            LocalKind::Uncounted | LocalKind::Borrowed => true,
            LocalKind::Slot => self.quiet(from, to),
            LocalKind::Owned if self.reaches_term(to) => {
                self.live_out[self.b].contains(s) || self.term_borrows(s)
            }
            LocalKind::Owned => self.used_again(s, from, to),
        }
    }

    /// Whether the value that the owned local `s` holds at statement `from`, which no
    /// statement up to `to` replaces, is used at `to` or after it. A use after a later
    /// statement gives `s` a new value reads the new one, and so does a successor of the block
    /// then.
    fn used_again(&self, s: Local, from: usize, to: usize) -> bool {
        let stmts = &self.block.stmts;
        let replaced = (from + 1..stmts.len())
            .find(|&i| matches!(stmts[i], Stmt::Assign(d, _) if d == s))
            .or_else(|| {
                term_defs(&self.block.term)
                    .any(|d| *d == s)
                    .then_some(stmts.len())
            });
        let until = replaced.unwrap_or(stmts.len());
        let used = self.sites[s.0 as usize].iter().any(|&(block, at)| {
            block == self.b && at.map_or(until == stmts.len(), |i| i >= to && i <= until)
        });
        used || (replaced.is_none() && self.live_out[self.b].contains(s))
    }

    /// Whether the terminator names `s`, and only borrows it, so that `s` lives through it and
    /// is released after it.
    fn term_borrows(&self, s: Local) -> bool {
        let uses = term_uses(&self.block.term);
        uses.iter().any(|&(m, _)| m == s) && borrows_only(&self.block.term, s)
    }

    /// Whether what the local that statement `def` defines borrows from lasts until after
    /// statement `to`.
    fn reads_last(&self, def: usize, to: usize) -> bool {
        let Stmt::Assign(_, r) = &self.block.stmts[def] else {
            return false;
        };
        self.quiet(def, to)
            && sources(r).is_some_and(|ss| ss.iter().all(|&x| self.outlives(x, def, to)))
    }

    /// Whether a statement after `from` up to `to` gives `s` a new value, or the terminator
    /// does when `to` reaches it.
    fn assigned(&self, s: Local, from: usize, to: usize) -> bool {
        self.between(from, to)
            .iter()
            .any(|st| matches!(st, Stmt::Assign(d, _) if *d == s))
            || (self.reaches_term(to) && term_defs(&self.block.term).any(|d| *d == s))
    }
}

/// Whether a terminator leaves memory as it is until control leaves it: a branch does, and so
/// does a call that takes no pointer. A return or a raise releases the slots.
fn term_quiet(t: &Terminator) -> bool {
    match t {
        Terminator::Goto(_) | Terminator::Branch { .. } | Terminator::Switch { .. } => true,
        Terminator::Call { args, .. } => !args.iter().any(|a| matches!(a, Arg::Ref(_))),
        Terminator::Return(_)
        | Terminator::Raise(_)
        | Terminator::Panic { .. }
        | Terminator::Unreachable => false,
    }
}

/// Whether a runtime function writes memory: an object made unique, an element or an entry
/// stored, or an element pushed.
fn writes(f: Runtime) -> bool {
    matches!(
        f,
        Runtime::Unique
            | Runtime::ListSlot
            | Runtime::ListSlotAt
            | Runtime::ListElement
            | Runtime::ListElementAt
            | Runtime::MapStore
            | Runtime::PropStore
            | Runtime::ListPush
            | Runtime::ListAppend
            | Runtime::ListPut
            | Runtime::StorePacked
    )
}
