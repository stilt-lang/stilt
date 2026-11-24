//! Which locals are owned, and where each is live: needed by a later use.

use stilt_mir::mir::{Block, Function, Local, ParamMode};

use crate::uses::{edge_def, stmt_uses, term_uses};

/// A set of locals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Set(Vec<u64>);

impl Set {
    pub(crate) fn new(n: usize) -> Self {
        Self(vec![0; n.div_ceil(64)])
    }

    pub(crate) fn contains(&self, l: Local) -> bool {
        self.contains_at(l.0 as usize)
    }

    pub(crate) fn insert(&mut self, l: Local) {
        self.insert_at(l.0 as usize);
    }

    pub(crate) fn remove(&mut self, l: Local) {
        self.remove_at(l.0 as usize);
    }

    /// Whether the set holds the member numbered `i`, for a set of what isn't a local, as the
    /// words in memory of `crate::slots` are numbered.
    pub(crate) fn contains_at(&self, i: usize) -> bool {
        self.0.get(i / 64).is_some_and(|w| w >> (i % 64) & 1 == 1)
    }

    pub(crate) fn insert_at(&mut self, i: usize) {
        self.0[i / 64] |= 1 << (i % 64);
    }

    pub(crate) fn remove_at(&mut self, i: usize) {
        self.0[i / 64] &= !(1 << (i % 64));
    }

    pub(crate) fn union(&self, other: &Self) -> Self {
        Self(self.0.iter().zip(&other.0).map(|(a, b)| a | b).collect())
    }

    pub(crate) fn minus(&self, other: &Self) -> Self {
        Self(self.0.iter().zip(&other.0).map(|(a, b)| a & !b).collect())
    }

    fn clear(&mut self) {
        self.0.fill(0);
    }

    fn copy_from(&mut self, other: &Self) {
        self.0.copy_from_slice(&other.0);
    }

    fn union_with(&mut self, other: &Self) {
        for (a, b) in self.0.iter_mut().zip(&other.0) {
            *a |= b;
        }
    }

    fn minus_with(&mut self, other: &Self) {
        for (a, b) in self.0.iter_mut().zip(&other.0) {
            *a &= !b;
        }
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = Local> + '_ {
        self.0.iter().enumerate().flat_map(|(i, &w)| {
            (0..64)
                .filter(move |b| w >> b & 1 == 1)
                .map(move |b| Local(u32::try_from(i * 64 + b).expect("under 4G locals")))
        })
    }
}

/// How a local's references are counted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LocalKind {
    /// A scalar, or a pointer to a slot.
    Uncounted,
    /// It owns its value, which is released after its last use.
    Owned,
    /// It borrows its value from a caller or an object that outlives it.
    Borrowed,
    /// It lives in memory, and owns what its slot holds.
    Slot,
}

#[derive(Debug)]
pub(crate) struct Kinds(Vec<LocalKind>);

impl Kinds {
    pub(crate) fn of(f: &Function) -> Self {
        let mut kinds: Vec<LocalKind> = f
            .locals
            .iter()
            .map(|d| match (d.repr.counted(), d.borrowed, d.slot) {
                (false, ..) => LocalKind::Uncounted,
                (true, true, _) => LocalKind::Borrowed,
                (true, false, true) => LocalKind::Slot,
                (true, false, false) => LocalKind::Owned,
            })
            .collect();
        for p in &f.params {
            let kind = &mut kinds[p.local.0 as usize];
            match p.mode {
                ParamMode::Ref => *kind = LocalKind::Uncounted,
                ParamMode::Borrowed if *kind != LocalKind::Uncounted => *kind = LocalKind::Borrowed,
                ParamMode::Borrowed | ParamMode::Owned => {}
            }
        }
        Self(kinds)
    }

    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn kind(&self, l: Local) -> LocalKind {
        self.0[l.0 as usize]
    }

    /// Makes an owned local borrow its value instead ([`crate::borrow`]).
    pub(crate) fn borrow(&mut self, l: Local) {
        self.0[l.0 as usize] = LocalKind::Borrowed;
    }

    pub(crate) fn owned(&self, l: Local) -> bool {
        self.kind(l) == LocalKind::Owned
    }

    /// The locals that live in memory and own what their slots hold.
    pub(crate) fn slots(&self) -> impl Iterator<Item = Local> + '_ {
        self.0
            .iter()
            .enumerate()
            .filter(|(_, k)| **k == LocalKind::Slot)
            .map(|(i, _)| Local(u32::try_from(i).expect("under 4G locals")))
    }
}

/// What a block does to the owned locals live at its end, which [`live_in`] reads at each step
/// of its iteration: the locals live on entry whatever is live at its end (`used`), those its
/// definitions end (`defined`), and each successor with the locals its edge to it defines.
struct Transfer<'f> {
    used: Set,
    defined: Set,
    succs: Vec<(usize, &'f [Local])>,
}

impl<'f> Transfer<'f> {
    /// The transfer of a block, read backward from its terminator: each statement's definition
    /// ends what was live, and then its uses of owned locals make them live.
    fn of(block: &'f Block, kinds: &Kinds, n: usize) -> Self {
        let (mut used, mut defined) = (Set::new(n), Set::new(n));
        for (l, _) in term_uses(&block.term) {
            if kinds.owned(l) {
                used.insert(l);
            }
        }
        for stmt in block.stmts.iter().rev() {
            let (named, def) = stmt_uses(stmt);
            if let Some((d, _)) = def {
                used.remove(d);
                defined.insert(d);
            }
            for (l, _) in named {
                if kinds.owned(l) {
                    used.insert(l);
                }
            }
        }
        let succs = block
            .term
            .successors()
            .into_iter()
            .map(|s| (s.0 as usize, edge_def(&block.term, s)))
            .collect();
        Self {
            used,
            defined,
            succs,
        }
    }
}

/// The owned locals live on entry to each block, found by iterating to a fixed point. Each
/// block's statements are read once, into its [`Transfer`], so that each step of the
/// iteration only combines sets.
pub(crate) fn live_in(f: &Function, kinds: &Kinds) -> Vec<Set> {
    let n = f.locals.len();
    let transfers: Vec<Transfer> = f.blocks.iter().map(|b| Transfer::of(b, kinds, n)).collect();
    let mut live = vec![Set::new(n); f.blocks.len()];
    let (mut set, mut needed) = (Set::new(n), Set::new(n));
    let mut changed = true;
    while changed {
        changed = false;
        for (b, t) in transfers.iter().enumerate().rev() {
            set.clear();
            for &(s, defs) in &t.succs {
                needed.copy_from(&live[s]);
                for &d in defs {
                    needed.remove(d);
                }
                set.union_with(&needed);
            }
            set.minus_with(&t.defined);
            set.union_with(&t.used);
            if set != live[b] {
                live[b].copy_from(&set);
                changed = true;
            }
        }
    }
    live
}
