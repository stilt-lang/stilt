//! Where the words in memory are read again (values.consumed-parameters and
//! values.inout-arguments). A word in memory is the slot of a local that lives there, or a word of
//! the value an `inout` parameter points to. A local in a register is read through its name, but a
//! word in memory is read through a pointer to it and through the locals that borrow from it, and a
//! slot by its name as well, so a word is *read again* after a point when any of those is used on
//! some path from there. Computing a pointer from another reads nothing.
//!
//! An `inout` parameter's words are also read where the function returns or raises, which gives
//! them back to the caller (values.inout-arguments), and nowhere a panic ends it, since nothing
//! reads anything after one. A store through a pointer to one of those words alone gives the word a
//! new value, so nothing before it reads the word through it: an assignment to the whole parameter
//! ends what is read of its value, as one to a local does.
//!
//! A statement that consumes a word nothing reads again gives its reference up, as a last use of
//! a local in a register does, and leaves the word holding nothing, so that the release at the
//! function's end, or the store that gives the word a new value, finds nothing to release.

use stilt_mir::mir::{
    Arg, Callee, Function, Local, Operand, ParamMode, Repr, Rvalue, Stmt, Terminator,
};

use crate::Need;
use crate::borrow::sources;
use crate::consume::definitions;
use crate::liveness::{Kinds, LocalKind, Set};
use crate::uses::{edge_def, stmt_uses, term_uses};

/// What makes a word of an `inout` parameter's value needed: the body reads it again, or the
/// caller does, when the function returns or when it raises. Each is a member of its own in the
/// sets of words read again, so that one pass finds them all.
#[derive(Clone, Copy)]
enum Mark {
    Read,
    Returned,
    Raised,
}

/// The number of [`Mark`]s.
const MARKS: usize = 3;

/// The words in memory, and which are read again at each block's start. A slot is numbered by its
/// local, and each word of an `inout` parameter after the locals, once for each [`Mark`].
pub(crate) struct Flow {
    locals: usize,
    /// The words of `inout` parameters that some pointer points to alone: each word's parameter,
    /// and its offset in the parameter's value.
    params: Vec<(Local, u32)>,
    /// For each local, the words that using it reads: a slot, those a pointer reaches, or those a
    /// local that borrows reads from.
    reads: Vec<Vec<usize>>,
    /// For each local that holds a pointer to one word of `params` alone, that word.
    exact: Vec<Option<usize>>,
    /// The words that a pointer to them leaves in places this analysis doesn't follow.
    pinned: Set,
    live_in: Vec<Set>,
    /// Whether each local holds an array in memory, which a load copies whole and never takes
    /// a word's reference from (`stilt_mir::mir::Repr::Array`).
    arrays: Vec<bool>,
}

impl Flow {
    pub(crate) fn of(f: &Function, kinds: &Kinds) -> Self {
        let n = f.locals.len();
        let (params, exact) = param_words(f);
        let width = n + MARKS * params.len();
        let mut flow = Self {
            locals: n,
            params,
            reads: vec![Vec::new(); n],
            exact,
            pinned: Set::new(width),
            live_in: vec![Set::new(width); f.blocks.len()],
            arrays: f
                .locals
                .iter()
                .map(|d| matches!(d.repr, Repr::Array(_)))
                .collect(),
        };
        if kinds.slots().next().is_none() && flow.params.is_empty() {
            return flow;
        }
        flow.follow(f, kinds);
        flow.pin_escapes(f, kinds);
        flow.solve(f);
        flow
    }

    /// The number of the word `i` of `params`, for the mark `m`.
    fn word(&self, i: usize, m: Mark) -> usize {
        self.locals + MARKS * i + m as usize
    }

    /// Whether a slot may have its value handed over: no pointer to it leaves the places this
    /// analysis follows.
    pub(crate) fn movable(&self, l: Local) -> bool {
        !self.pinned.contains(l)
    }

    /// Whether using `other` reads the slot `l`.
    pub(crate) fn reads(&self, other: Local, l: Local) -> bool {
        self.reads[other.0 as usize].contains(&(l.0 as usize))
    }

    /// The word of an `inout` parameter's value that a statement loads, through the pointer it
    /// names, which points to that word alone, if no pointer to the word leaves the places this
    /// analysis follows: the pointer, the word, and the parameter.
    pub(crate) fn loaded(&self, s: &Stmt) -> Option<(Local, usize, Local)> {
        let Stmt::Assign(d, Rvalue::Load(Operand::Local(p))) = s else {
            return None;
        };
        if self.arrays[d.0 as usize] {
            return None;
        }
        let i = self.exact[p.0 as usize]?;
        let movable = !self.pinned.contains_at(self.word(i, Mark::Read));
        movable.then_some((*p, i, self.params[i].0))
    }

    /// What needs the word `i` of `params` after a statement that loads it, given the words read
    /// again after the statement, `after`, and after its block's terminator, `after_term`, or
    /// `None` when nothing does. A read before the terminator is the call's own: it is given the
    /// parameter twice.
    pub(crate) fn need(&self, i: usize, after: &Set, after_term: &Set) -> Option<Need> {
        let has = |set: &Set, m: Mark| set.contains_at(self.word(i, m));
        if has(after, Mark::Read) {
            return Some(if has(after_term, Mark::Read) {
                Need::After
            } else {
                Need::Twice
            });
        }
        let (returns, raises) = (has(after, Mark::Returned), has(after, Mark::Raised));
        (returns || raises).then_some(Need::Back { returns, raises })
    }

    /// The words read again after a block's terminator.
    pub(crate) fn after_block(&self, f: &Function, b: usize) -> Set {
        let term = &f.blocks[b].term;
        let mut after = Set::new(self.locals + MARKS * self.params.len());
        for s in term.successors() {
            let mut needed = self.live_in[s.0 as usize].clone();
            for &d in edge_def(term, s) {
                needed.remove(d);
            }
            after = after.union(&needed);
        }
        after
    }

    /// The words read again before a terminator, given those read again after it: a return or
    /// a raise gives the caller every word of the `inout` parameters.
    pub(crate) fn before_term(&self, t: &Terminator, mut live: Set) -> Set {
        let exit = match t {
            Terminator::Return(_) => Some(Mark::Returned),
            Terminator::Raise(_) => Some(Mark::Raised),
            _ => None,
        };
        if let Some(m) = exit {
            for i in 0..self.params.len() {
                live.insert_at(self.word(i, m));
            }
        }
        for (l, _) in term_uses(t) {
            self.add(&mut live, l);
        }
        live
    }

    /// Moves `live` from after a statement to before it.
    pub(crate) fn before_stmt(&self, s: &Stmt, live: &mut Set) {
        let (uses, def) = stmt_uses(s);
        if let Some((d, _)) = def {
            live.remove(d);
        }
        match s {
            Stmt::Store { slot, value, .. } => {
                match self.exact_of(slot) {
                    Some(i) => {
                        for m in [Mark::Read, Mark::Returned, Mark::Raised] {
                            live.remove_at(self.word(i, m));
                        }
                    }
                    None => self.add_operand(live, slot),
                }
                self.add_operand(live, value);
            }
            // A local that borrows the word it loads reads it where it is used.
            Stmt::Assign(d, Rvalue::Load(p)) => match self.exact_of(p) {
                Some(i) if self.reads[d.0 as usize].is_empty() => {
                    live.insert_at(self.word(i, Mark::Read));
                }
                Some(_) => {}
                None => self.add_operand(live, p),
            },
            Stmt::Assign(_, Rvalue::Offset(..)) => {}
            Stmt::Assign(_, Rvalue::Use(o)) if self.exact_of(o).is_some() => {}
            _ => {
                for (l, _) in uses {
                    self.add(live, l);
                }
            }
        }
    }

    /// The word of `params` that a pointer in `o` points to alone, if one.
    fn exact_of(&self, o: &Operand) -> Option<usize> {
        o.local().and_then(|p| self.exact[p.0 as usize])
    }

    fn add(&self, live: &mut Set, l: Local) {
        for &w in &self.reads[l.0 as usize] {
            live.insert_at(w);
        }
    }

    fn add_operand(&self, live: &mut Set, o: &Operand) {
        if let Some(l) = o.local() {
            self.add(live, l);
        }
    }

    /// Finds what each local reads, by iterating to a fixed point over the definitions.
    fn follow(&mut self, f: &Function, kinds: &Kinds) {
        for l in kinds.slots() {
            self.reads[l.0 as usize] = vec![l.0 as usize];
        }
        for i in 0..self.params.len() {
            let w = self.word(i, Mark::Read);
            self.reads[self.params[i].0.0 as usize].push(w);
        }
        let mut changed = true;
        while changed {
            changed = false;
            for stmt in f.blocks.iter().flat_map(|b| &b.stmts) {
                let Stmt::Assign(d, r) = stmt else { continue };
                for w in self.read_by(f, kinds, *d, r) {
                    let reads = &mut self.reads[d.0 as usize];
                    if !reads.contains(&w) {
                        reads.push(w);
                        changed = true;
                    }
                }
            }
        }
    }

    /// The words that `d` reads when `r` defines it: those a pointer reaches, or those a local
    /// that borrows reads from, which for a word loaded through a pointer to one word alone is
    /// that word.
    fn read_by(&self, f: &Function, kinds: &Kinds, d: Local, r: &Rvalue) -> Vec<usize> {
        let of = |ls: &[Local]| -> Vec<usize> {
            ls.iter()
                .flat_map(|l| self.reads[l.0 as usize].clone())
                .collect()
        };
        let one = |o: &Operand| -> Vec<usize> { of(&o.local().into_iter().collect::<Vec<_>>()) };
        if let (Rvalue::Load(p), LocalKind::Borrowed) = (r, kinds.kind(d))
            && let Some(i) = self.exact_of(p)
        {
            return vec![self.word(i, Mark::Read)];
        }
        match (r, kinds.kind(d)) {
            (Rvalue::SlotOf(s), _) => group(f, kinds, *s),
            (Rvalue::Offset(o, _) | Rvalue::FieldSlot { slot: o, .. }, _)
            | (Rvalue::Use(o), LocalKind::Uncounted | LocalKind::Borrowed) => one(o),
            (_, LocalKind::Borrowed) => sources(r).map(|s| of(&s)).unwrap_or_default(),
            _ => Vec::new(),
        }
    }

    /// Pins the words whose pointers are stored, returned or passed as values.
    fn pin_escapes(&mut self, f: &Function, kinds: &Kinds) {
        for block in &f.blocks {
            let mut escaping: Vec<&Operand> = Vec::new();
            for stmt in &block.stmts {
                match stmt {
                    Stmt::Assign(_, Rvalue::Alloc(_, fields)) => {
                        escaping.extend(fields.iter().map(|(o, _)| o));
                    }
                    Stmt::Assign(_, Rvalue::Prim(_, args, loc)) => {
                        escaping.extend(args.iter().chain([loc]));
                    }
                    Stmt::Store { value, .. } => escaping.push(value),
                    _ => {}
                }
            }
            match &block.term {
                Terminator::Call { callee, args, .. } => {
                    if let Callee::Value(o) | Callee::Method(o, _) = callee {
                        escaping.push(o);
                    }
                    for a in args {
                        if let Arg::Borrow(o) | Arg::Own(o) = a {
                            escaping.push(o);
                        }
                    }
                }
                Terminator::Return(os) | Terminator::Raise(os) => escaping.extend(os),
                _ => {}
            }
            for l in escaping.into_iter().filter_map(Operand::local) {
                if kinds.kind(l) == LocalKind::Uncounted {
                    for &w in &self.reads[l.0 as usize] {
                        self.pinned.insert_at(w);
                    }
                }
            }
        }
    }

    /// Finds the words read again at each block's start, by iterating to a fixed point.
    fn solve(&mut self, f: &Function) {
        let mut changed = true;
        while changed {
            changed = false;
            for b in (0..f.blocks.len()).rev() {
                let block = &f.blocks[b];
                let mut live = self.before_term(&block.term, self.after_block(f, b));
                for stmt in block.stmts.iter().rev() {
                    self.before_stmt(stmt, &mut live);
                }
                if live != self.live_in[b] {
                    self.live_in[b] = live;
                    changed = true;
                }
            }
        }
    }
}

/// The words of `inout` parameters that pointers point to alone, each as its parameter and its
/// offset, and for each local, the one it points to, if any: an `inout` parameter points to the
/// first word of its value, and a pointer that one definition makes an offset or a copy of such a
/// pointer to the word that gives.
fn param_words(f: &Function) -> (Vec<(Local, u32)>, Vec<Option<usize>>) {
    if f.params.iter().all(|p| p.mode != ParamMode::Ref) {
        return (Vec::new(), vec![None; f.locals.len()]);
    }
    let defs = definitions(f);
    let mut at: Vec<Option<(Local, u32)>> = vec![None; f.locals.len()];
    for p in &f.params {
        if p.mode == ParamMode::Ref && defs[p.local.0 as usize] == 1 {
            at[p.local.0 as usize] = Some((p.local, 0));
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for stmt in f.blocks.iter().flat_map(|b| &b.stmts) {
            let Stmt::Assign(d, r) = stmt else { continue };
            let from = |o: &Operand| o.local().and_then(|l| at[l.0 as usize]);
            let word = match r {
                Rvalue::Offset(o, words) => from(o).map(|(param, at)| (param, at + words)),
                Rvalue::Use(o) => from(o),
                _ => None,
            };
            if word.is_some() && defs[d.0 as usize] == 1 && at[d.0 as usize] != word {
                at[d.0 as usize] = word;
                changed = true;
            }
        }
    }
    let mut params: Vec<(Local, u32)> = Vec::new();
    let mut index = |w: (Local, u32)| {
        params.iter().position(|&v| v == w).unwrap_or_else(|| {
            params.push(w);
            params.len() - 1
        })
    };
    let exact = at.into_iter().map(|w| w.map(&mut index)).collect();
    (params, exact)
}

/// The slots of the value in memory that includes the slot `l`: its words.
fn group(f: &Function, kinds: &Kinds, l: Local) -> Vec<usize> {
    let mut first = l.0 as usize;
    while f.locals[first].grouped && first > 0 {
        first -= 1;
    }
    let mut out = Vec::new();
    let mut i = first;
    while i < f.locals.len() && (i == first || (f.locals[i].slot && f.locals[i].grouped)) {
        let w = Local(u32::try_from(i).expect("under 4G locals"));
        if kinds.kind(w) == LocalKind::Slot {
            out.push(i);
        }
        i += 1;
    }
    out
}

#[cfg(test)]
mod tests;
