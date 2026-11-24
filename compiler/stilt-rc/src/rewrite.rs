//! The counting of a block's statements: copies before the statements that consume what is still
//! needed, releases after the last use, and the handover of a word in memory at its last use.

use stilt_mir::FnRef;
use stilt_mir::mir::{Arg, Block, BlockId, Callee, Local, Operand, Repr, Rvalue, Stmt, Terminator};

use crate::liveness::{Kinds, LocalKind, Set};
use crate::slots::Flow;
use crate::uses::{Def, Use, stmt_uses};
use crate::{Copied, Need, dups_needed, tally};

/// A direct call: the callee, the location of its call, and the locals it consumes.
type OwnCall = (FnRef, u64, Vec<Local>);

/// What counting a block's statements needs besides the locals: the function's words in memory,
/// the block, and the words read again after its terminator.
pub(crate) struct Counting<'a> {
    pub(crate) kinds: &'a Kinds,
    pub(crate) flow: &'a Flow,
    pub(crate) id: BlockId,
    pub(crate) after_term: &'a Set,
}

impl Counting<'_> {
    /// Whether a statement that names `uses` and defines `def` can give up the reference that
    /// the slot `l` holds: nothing reads the slot again on any path after it, no other local it
    /// names reads the slot, and it doesn't define the slot (values.consumed-parameters).
    fn hands_over(&self, l: Local, after: &Set, uses: &[(Local, Use)], def: Option<Def>) -> bool {
        self.flow.movable(l)
            && !after.contains(l)
            && def.is_none_or(|(d, _)| d != l)
            && uses.iter().all(|&(o, _)| o == l || !self.flow.reads(o, l))
    }

    /// The counting that `stmt`'s definition of `d` needs, before it and after it, `live` being
    /// the owned locals live after it and `slots` the words read again after it. An owned local
    /// that keeps a word it loads of an `inout` parameter's value takes the word's reference when
    /// nothing needs the word after it, as the last use of a slot does, and leaves the word holding
    /// nothing until a store gives it a new value (values.consumed-parameters and
    /// values.inout-arguments). Otherwise its copy of the word, if a direct call consumes it, is a
    /// lost reuse, which goes to `copied`.
    fn define(
        &self,
        stmt: &Stmt,
        (d, fresh): Def,
        live: &Set,
        slots: &Set,
        call: Option<&OwnCall>,
        copied: &mut Vec<Copied>,
    ) -> (Vec<Stmt>, Vec<Stmt>) {
        let (mut before, mut after) = (Vec::new(), Vec::new());
        let live = live.contains(d);
        let loaded = self
            .flow
            .loaded(stmt)
            .filter(|_| live && self.kinds.owned(d));
        if let Some((p, word, param)) = loaded {
            let Some(need) = self.flow.need(word, slots, self.after_term) else {
                after.push(Stmt::Store {
                    slot: Operand::Local(p),
                    value: Operand::word(0),
                    repr: Repr::Scalar,
                });
                return (before, after);
            };
            copied.extend(call.and_then(|c| self.load_copy(c, d, param, need)));
        }
        def_counting(self.kinds, d, fresh, live, &mut before, &mut after);
        (before, after)
    }

    /// The copy that `call` consumes of the word loaded into `d`, of the value of the `inout`
    /// parameter `param`, if it consumes `d`.
    fn load_copy(&self, call: &OwnCall, d: Local, param: Local, need: Need) -> Option<Copied> {
        let (callee, at, owned) = call;
        owned.contains(&d).then(|| Copied {
            block: self.id,
            local: param,
            callee: callee.clone(),
            need,
            at: *at,
        })
    }
}

/// The direct call that ends a block, if one does.
fn own_call(block: &Block) -> Option<OwnCall> {
    let Terminator::Call {
        callee: Callee::Direct(callee),
        args,
        ..
    } = &block.term
    else {
        return None;
    };
    let at = block.stmts.iter().rev().find_map(|s| match s {
        Stmt::At(word) => Some(*word),
        _ => None,
    });
    let owned = args.iter().filter_map(|a| match a {
        Arg::Own(Operand::Local(l)) => Some(*l),
        _ => None,
    });
    Some((callee.clone(), at.unwrap_or(0), owned.collect()))
}

/// Rewrites a block's statements from the last to the first, `live` being the owned locals
/// live after them and `slots` the words in memory read again after them. A statement that
/// consumes a slot nothing reads again gives its reference up and clears the slot, unless the
/// block ends the function and nothing writes the slot after it, when the release at the end
/// finds it empty, and so does a load of a word of an `inout` parameter's value into a local
/// that keeps it ([`Counting::define`]). A copy of either that a direct call consumes is a lost
/// reuse, which goes to `copied`.
pub(crate) fn rewrite_stmts(
    block: &mut Block,
    cx: &Counting,
    mut live: Set,
    mut slots: Set,
    copied: &mut Vec<Copied>,
) {
    let kinds = cx.kinds;
    let call = own_call(block);
    let ends = matches!(block.term, Terminator::Return(_) | Terminator::Raise(_));
    let (mut handed, mut written) = (Vec::new(), Set::new(kinds.len()));
    let stmts = std::mem::take(&mut block.stmts);
    let mut out: Vec<Vec<Stmt>> = Vec::with_capacity(stmts.len());
    for stmt in stmts.into_iter().rev() {
        let (uses, def) = counted_uses(&stmt, kinds);
        let (mut before, mut after_stmt) = def.map_or_else(Default::default, |def| {
            cx.define(&stmt, def, &live, &slots, call.as_ref(), copied)
        });
        if let Some((d, _)) = def {
            live.remove(d);
            written.insert(d);
        }
        for (l, consumes, borrows) in tally(&uses) {
            let slot = kinds.kind(l) == LocalKind::Slot;
            let kept = if slot {
                !cx.hands_over(l, &slots, &uses, def)
            } else {
                live.contains(l)
            };
            let dups = dups_needed(kinds, l, consumes, borrows, kept);
            before.extend(std::iter::repeat_n(Stmt::Dup(l), dups));
            if slot && dups > 0 {
                copied.extend(slot_copy(cx.id, call.as_ref(), &stmt, l));
            }
            if slot && dups < consumes {
                if ends && !written.contains(l) {
                    handed.push(l);
                } else {
                    after_stmt.push(Stmt::Assign(l, Rvalue::Use(Operand::word(0))));
                }
            }
            if kinds.owned(l) && (consumes == 0 || borrows > 0) && !live.contains(l) {
                after_stmt.push(Stmt::Drop(l));
            }
        }
        for (l, _) in &uses {
            if kinds.owned(*l) {
                live.insert(*l);
            }
        }
        cx.flow.before_stmt(&stmt, &mut slots);
        let mut group = before;
        group.push(stmt);
        group.extend(after_stmt);
        out.push(group);
    }
    block.stmts = out.into_iter().rev().flatten().collect();
    for l in handed {
        let last = block.stmts.iter().rposition(|s| *s == Stmt::Drop(l));
        block
            .stmts
            .remove(last.expect("a block that ends the function drops its slots"));
    }
}

/// The copy of the slot `l` that `stmt` makes for a direct call to consume, if it does.
fn slot_copy(id: BlockId, call: Option<&OwnCall>, stmt: &Stmt, l: Local) -> Option<Copied> {
    let (callee, at, owned) = call?;
    let Stmt::Assign(d, Rvalue::Use(Operand::Local(s))) = stmt else {
        return None;
    };
    (*s == l && owned.contains(d)).then(|| Copied {
        block: id,
        local: l,
        callee: callee.clone(),
        need: Need::After,
        at: *at,
    })
}

/// What a statement does to the locals it names, where a copy into a local that borrows reads
/// what it copies and takes no reference ([`aliases`]).
fn counted_uses(stmt: &Stmt, kinds: &Kinds) -> (Vec<(Local, Use)>, Option<Def>) {
    let (mut uses, def) = stmt_uses(stmt);
    match stmt {
        Stmt::Assign(d, Rvalue::Use(_)) if kinds.kind(*d) == LocalKind::Borrowed => {
            for u in &mut uses {
                u.1 = Use::Borrow;
            }
            (uses, Some((*d, false)))
        }
        _ => (uses, def),
    }
}

/// The counting a definition of `d` needs: a copy of a borrowed word, a release of a value
/// nothing uses, and before an assignment to a local in memory, the release of what it held.
fn def_counting(
    kinds: &Kinds,
    d: Local,
    fresh: bool,
    live: bool,
    before: &mut Vec<Stmt>,
    after: &mut Vec<Stmt>,
) {
    match kinds.kind(d) {
        LocalKind::Owned => match (fresh, live) {
            (true, false) => after.push(Stmt::Drop(d)),
            (false, true) => after.push(Stmt::Dup(d)),
            (true, true) | (false, false) => {}
        },
        LocalKind::Slot => {
            before.push(Stmt::Drop(d));
            if !fresh {
                after.push(Stmt::Dup(d));
            }
        }
        LocalKind::Borrowed | LocalKind::Uncounted => {}
    }
}
