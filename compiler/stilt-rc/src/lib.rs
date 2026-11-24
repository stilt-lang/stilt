//! Reference counting for Stilt's MIR, in the manner of Perceus (Compiler architecture,
//! "Reference counting"): every owned local is released just after its last use, and copied
//! only where a use consumes it while it is still needed. Nothing is held longer than the code
//! needs it, which lets copy-on-write change a value in place whenever no other value shares it.
//!
//! A function owns the parameters it consumes, which [`consumed`] infers
//! (values.consumed-parameters), and borrows the others, so that a caller passing its last use of a
//! value gives the value up and the callee can change it in place ([`consume`]). A caller that
//! keeps using a value it passes to a consumed parameter copies it before the call, and the callee
//! then gets it still shared: the call loses reuse, which [`losing_reuse`] gives. Calls through
//! values borrow every `let` parameter, and the adapters that call a function directly give it what
//! it consumes.
//!
//! A local that lives in memory, because a pointer to it is taken, is the exception: it owns
//! whatever its slot holds, which an assignment releases before it writes, and which the
//! function releases when it returns or raises. A use that consumes it copies it, unless nothing
//! reads the slot again, by its name, through a pointer to it or through a local that borrows
//! from it, on any path after: then the use takes the slot's reference and clears the slot
//! ([`slots`]), as the last use of a local in a register does. A word of the value an `inout`
//! parameter points to is handed over in the same way, when a local that keeps it loads it and
//! every path after assigns the word before the function reads it, returns or raises, which
//! gives the word back to the caller (values.inout-arguments). A local that only reads what another
//! value holds borrows it, and is never counted ([`borrow`], [`aliases`]).
//!
//! The modes of a function's bindings are facts beside consumption: where a local escapes, where
//! a `var` is written while shared, and which closures and parameters run at most once
//! ([`modes()`], modes.escaping, modes.shared-writes and modes.once-closures).
//!
//! Its place among the crates (`compiler/README.md`): it depends on `stilt-diag`, `stilt-syntax`,
//! `stilt-db`, `stilt-hir`, `stilt-types` and `stilt-mir`, and on no back end.
#![warn(missing_docs)]

mod aliases;
mod borrow;
mod cache;
pub mod consume;
mod fixpoint;
mod liveness;
mod lost;
mod modes;
mod promises;
mod queries;
mod reach;
mod reuse;
mod rewrite;
mod slots;
mod unique;
mod uses;

use stilt_mir::FnRef;
use stilt_mir::mir::{Block, BlockId, Callee, Function, Local, ParamMode, Stmt, Terminator};

pub use crate::cache::Counted;
use crate::consume::{Conventions, apply};
use crate::liveness::{Kinds, LocalKind, Set, live_in};
pub use crate::lost::{LostReuse, Need, losing_reuse};
pub use crate::modes::{
    Escape, How, Modes, Modification, Once, Shared, SharedWrite, Stored, modes, shared_writes,
};
pub use crate::promises::{body_errors, check_in_parallel, copy_causes};
pub use crate::queries::{Consuming, consumed, consuming, conventions};
pub use crate::reach::Reach;
use crate::rewrite::{Counting, rewrite_stmts};
use crate::slots::Flow;
use crate::uses::{Use, edge_def, term_uses};

/// A copy that reference counting makes of a value that a direct call consumes, because the
/// function still needs it: it uses the value after the call, the call names it again, or it is
/// the value of an `inout` parameter, which goes back to the caller. The callee then gets a value
/// that is still shared, and can't reuse its memory (values.consumed-parameters and
/// values.inout-arguments).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Copied {
    /// The block that the call ends.
    pub(crate) block: BlockId,
    /// The local that holds the value, or the `inout` parameter that points to it.
    pub(crate) local: Local,
    pub(crate) callee: FnRef,
    pub(crate) need: Need,
    /// The location word of the call, as [`Stmt::At`] marks it, or 0 when no marker comes
    /// before it in its block.
    pub(crate) at: u64,
}

/// A function's MIR as a build gives it to code generation: with the conventions that
/// consumption calls for, optimized, and with its reference counting, its new objects built in
/// the memory that releases before them keep where they can ([`reuse`]), before the
/// optimizations that read the counting. With it, the copies that the counting makes of what direct calls
/// consume.
pub(crate) fn counted(before: &Function, conventions: &Conventions) -> (Function, Vec<Copied>) {
    let mut after = before.clone();
    apply(&mut after, conventions);
    stilt_mir::opt::optimize(&mut after);
    let copied = count(&mut after);
    reuse::reuse(&mut after);
    unique::make_unique(&mut after, &conventions.unique);
    (after, copied)
}

/// Inserts the reference counting of a function.
///
/// # Panics
///
/// Panics when the function has 2³² blocks or more.
pub fn insert(f: &mut Function) {
    count(f);
}

/// Inserts the reference counting of a function, and gives the copies it makes of owned
/// locals that direct calls consume.
fn count(f: &mut Function) -> Vec<Copied> {
    let kinds = borrowing(f);
    let live = live_in(f, &kinds);
    let flow = Flow::of(f, &kinds);
    let slots_after: Vec<Set> = (0..f.blocks.len())
        .map(|b| flow.after_block(f, b))
        .collect();
    let mut edges: Vec<(BlockId, BlockId, Vec<Local>)> = Vec::new();
    let mut copied = Vec::new();
    for (b, slots_after) in slots_after.iter().enumerate() {
        let id = BlockId(u32::try_from(b).expect("under 4G blocks"));
        let after = live_after(f, id, &live);
        let block = &mut f.blocks[b];
        let borrowed_only = rewrite_term(block, id, &kinds, &after, &mut copied);
        let cx = Counting {
            kinds: &kinds,
            flow: &flow,
            id,
            after_term: slots_after,
        };
        let slots = flow.before_term(&block.term, slots_after.clone());
        rewrite_stmts(
            block,
            &cx,
            after.union(&term_live(&block.term, &kinds)),
            slots,
            &mut copied,
        );
        for s in block.term.successors() {
            if edges.iter().any(|(from, to, _)| *from == id && *to == s) {
                continue;
            }
            let mut owned = after.clone();
            for &l in &borrowed_only {
                owned.insert(l);
            }
            for &d in edge_def(&block.term, s) {
                if kinds.owned(d) {
                    owned.insert(d);
                }
            }
            let drops: Vec<Local> = owned.minus(&live[s.0 as usize]).iter().collect();
            edges.push((id, s, drops));
        }
    }
    entry_drops(f, &kinds, &live[0]);
    place_edge_drops(f, edges);
    copied
}

/// How each local of a function is counted, with the locals that can borrow borrowing.
fn borrowing(f: &Function) -> Kinds {
    let mut kinds = Kinds::of(f);
    for l in aliases::inferred(f, &kinds) {
        kinds.borrow(l);
    }
    let live = live_in(f, &kinds);
    let live_out: Vec<Set> = (0..f.blocks.len())
        .map(|b| {
            live_after(
                f,
                BlockId(u32::try_from(b).expect("under 4G blocks")),
                &live,
            )
        })
        .collect();
    for l in borrow::inferred(f, &kinds, &live_out) {
        kinds.borrow(l);
    }
    kinds
}

/// The owned locals live after a block's terminator: those its successors need, but for what
/// the terminator itself defines on the way to each.
fn live_after(f: &Function, b: BlockId, live: &[Set]) -> Set {
    let term = &f.blocks[b.0 as usize].term;
    let mut after = Set::new(f.locals.len());
    for s in term.successors() {
        let mut needed = live[s.0 as usize].clone();
        for &d in edge_def(term, s) {
            needed.remove(d);
        }
        after = after.union(&needed);
    }
    after
}

/// The owned locals a terminator names.
fn term_live(t: &Terminator, kinds: &Kinds) -> Set {
    let mut set = Set::new(kinds.len());
    for (l, _) in term_uses(t) {
        if kinds.owned(l) {
            set.insert(l);
        }
    }
    set
}

/// Copies what a terminator consumes while it is still needed, and before a return or a raise,
/// releases the locals in memory. Returns the owned locals whose last use is the terminator's
/// borrow, which every edge out of it releases: one it only borrows, and one it also consumes,
/// whose copies it gives away while it keeps the reference it borrows. Each copy of an owned
/// local that a direct call consumes goes to `copied`.
fn rewrite_term(
    block: &mut Block,
    id: BlockId,
    kinds: &Kinds,
    after: &Set,
    copied: &mut Vec<Copied>,
) -> Vec<Local> {
    let uses = term_uses(&block.term);
    let mut borrowed_only = Vec::new();
    let returns = matches!(block.term, Terminator::Return(_) | Terminator::Raise(_));
    let mut handed = Vec::new();
    for (l, consumes, borrows) in tally(&uses) {
        let slot = kinds.kind(l) == LocalKind::Slot;
        // A slot is read again after any terminator but the ones that end the function.
        let blocked = if slot { !returns } else { after.contains(l) };
        let dups = dups_needed(kinds, l, consumes, borrows, blocked);
        if dups > 0 && kinds.owned(l) {
            copied.extend(call_copy(block, id, l, after.contains(l)));
        }
        block.stmts.extend(std::iter::repeat_n(Stmt::Dup(l), dups));
        if slot && dups < consumes {
            handed.push(l);
        }
        if kinds.owned(l) && (consumes == 0 || borrows > 0) && !after.contains(l) {
            borrowed_only.push(l);
        }
    }
    if returns {
        let held = kinds.slots().filter(|l| !handed.contains(l));
        block.stmts.extend(held.map(Stmt::Drop));
    }
    borrowed_only
}

/// The copy of `local` that the terminator of `block` consumes, if it is a direct call.
fn call_copy(block: &Block, id: BlockId, local: Local, after: bool) -> Option<Copied> {
    let Terminator::Call {
        callee: Callee::Direct(callee),
        ..
    } = &block.term
    else {
        return None;
    };
    let at = block.stmts.iter().rev().find_map(|s| match s {
        Stmt::At(word) => Some(*word),
        _ => None,
    });
    Some(Copied {
        block: id,
        local,
        callee: callee.clone(),
        need: if after { Need::After } else { Need::Twice },
        at: at.unwrap_or(0),
    })
}

/// Each local a statement names, in the order it first names them, with how many times it
/// consumes and borrows it. A statement may name tens of thousands of locals, the words of a
/// large array (generics.large-arrays), so each is found by its index, not by a search.
pub(crate) fn tally(uses: &[(Local, Use)]) -> Vec<(Local, usize, usize)> {
    let mut out: Vec<(Local, usize, usize)> = Vec::new();
    let mut index: std::collections::HashMap<Local, usize> = std::collections::HashMap::new();
    for &(l, how) in uses {
        let i = *index.entry(l).or_insert_with(|| {
            out.push((l, 0, 0));
            out.len() - 1
        });
        match how {
            Use::Consume => out[i].1 += 1,
            Use::Borrow => out[i].2 += 1,
        }
    }
    out
}

/// How many copies a statement needs of a local it consumes `consumes` times and borrows
/// `borrows` times: one per consuming use, but for the last of an owned local or a slot not needed after.
pub(crate) fn dups_needed(
    kinds: &Kinds,
    l: Local,
    consumes: usize,
    borrows: usize,
    live_after: bool,
) -> usize {
    match kinds.kind(l) {
        LocalKind::Uncounted => 0,
        LocalKind::Borrowed => consumes,
        LocalKind::Owned | LocalKind::Slot if live_after || borrows > 0 => consumes,
        LocalKind::Owned | LocalKind::Slot => consumes.saturating_sub(1),
    }
}

/// Releases the owned parameters that the body never uses.
fn entry_drops(f: &mut Function, kinds: &Kinds, live: &Set) {
    let unused: Vec<Stmt> = f
        .params
        .iter()
        .filter(|p| p.mode == ParamMode::Owned && kinds.owned(p.local) && !live.contains(p.local))
        .map(|p| Stmt::Drop(p.local))
        .collect();
    let entry = &mut f.blocks[0];
    entry.stmts.splice(0..0, unused);
}

/// Puts the releases of each edge at the start of its target, when the edge is the only way
/// into it, and otherwise in a block of their own on the edge.
fn place_edge_drops(f: &mut Function, edges: Vec<(BlockId, BlockId, Vec<Local>)>) {
    let mut preds = vec![0usize; f.blocks.len()];
    for (_, to, _) in &edges {
        preds[to.0 as usize] += 1;
    }
    for (from, to, drops) in edges {
        if drops.is_empty() {
            continue;
        }
        let drops: Vec<Stmt> = drops.into_iter().map(Stmt::Drop).collect();
        if preds[to.0 as usize] == 1 {
            f.blocks[to.0 as usize].stmts.splice(0..0, drops);
            continue;
        }
        let split = BlockId(u32::try_from(f.blocks.len()).expect("under 4G blocks"));
        f.blocks.push(Block {
            stmts: drops,
            term: Terminator::Goto(to),
        });
        retarget_edge(&mut f.blocks[from.0 as usize].term, to, split);
    }
}

/// Makes each edge of a terminator to block `old` go to block `new` instead.
pub(crate) fn retarget_edge(term: &mut Terminator, old: BlockId, new: BlockId) {
    let swap = |b: &mut BlockId| {
        if *b == old {
            *b = new;
        }
    };
    match term {
        Terminator::Goto(b) => swap(b),
        Terminator::Branch {
            then, otherwise, ..
        } => {
            swap(then);
            swap(otherwise);
        }
        Terminator::Switch {
            cases, otherwise, ..
        } => {
            for (_, b) in cases.iter_mut() {
                swap(b);
            }
            swap(otherwise);
        }
        Terminator::Call { next, raised, .. } => {
            swap(next);
            if let Some((_, b)) = raised.as_mut() {
                swap(b);
            }
        }
        Terminator::Return(_)
        | Terminator::Raise(_)
        | Terminator::Panic { .. }
        | Terminator::Unreachable => {}
    }
}
