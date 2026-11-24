//! Lists whose header C locals hold: the list a `var` holds in memory, and the
//! list a local holds, each with its length and its elements' address, so that a loop that
//! reads and writes a list's elements reads its header once. C can't do this itself: under
//! `-fno-strict-aliasing` a store to an element may write any word, so clang reloads the
//! header after each.
//!
//! The header changes only when the list is changed in place, which takes a list that nothing
//! else references, through the place that holds it or the local that does, and a store to an
//! element writes into the list's elements, which are no header and no place of the function.
//! So the locals stay right across element stores, and are given up at what may change a list:
//! an assignment to the place or the local, a call, and any runtime function but those that
//! read an element, take an element's slot or make the place's list unique, which the code
//! below does with the locals and then sets them.
//!
//! A place is a local that lives in memory, or the caller's slot that an `inout` parameter
//! points to, which nothing but the parameter reaches while the call runs.
//!
//! Which locals are right where each block starts is a forward analysis over the function's
//! blocks, the meet of their predecessors', with the same [`State::step`] that the emitter
//! follows, so the two agree on every path.

use std::collections::{BTreeSet, HashMap};

mod scan;

use scan::{named_lists, origins};

use stilt_mir::mir::{
    Arg, Callee, Const, Function, Operand, ParamMode, Runtime, Rvalue, Stmt, Terminator,
    UNIQUE_LIST,
};
use stilt_mir::{FnRef, shape};

/// A list whose header locals may hold: the one a local of the function holds in memory, a
/// place, or the one a local holds as a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Key {
    Place(usize),
    Value(usize),
}

/// What is known where a statement starts: whose header the locals hold, and which locals hold
/// what a place held when they were read from it, since nothing changed it.
#[derive(Clone, Debug, Default)]
pub(crate) struct State {
    pub(crate) held: BTreeSet<Key>,
    copies: HashMap<usize, usize>,
}

/// The lists of a function: what each block knows where it starts, the state of the statement
/// being emitted, and every key whose locals the code uses.
#[derive(Debug, Default)]
pub(crate) struct Lists {
    /// The place each local that only ever points to one points to.
    origin: Vec<Option<usize>>,
    slot: Vec<bool>,
    /// The places and parameters that hold lists, which list operations name: each assignment
    /// of a place gives it a list, and a parameter holds one from the start.
    named: Vec<bool>,
    /// The parameters that hold lists, whose headers the locals hold from the start.
    pub(crate) params: Vec<usize>,
    /// The lists of the `let` parameters that the function doesn't consume, which nothing
    /// changes while it runs: its caller keeps them, so no code it runs holds one alone.
    lent: BTreeSet<Key>,
    ins: Vec<BTreeSet<Key>>,
    pub(crate) state: State,
    pub(crate) used: BTreeSet<Key>,
}

impl Lists {
    pub(crate) fn new(f: &Function) -> Self {
        let origin = origins(f);
        let slot: Vec<bool> = f.locals.iter().map(|d| d.slot).collect();
        let named = named_lists(f, &origin, &slot);
        let params: Vec<usize> = (f.params.iter())
            .filter(|p| p.mode != ParamMode::Ref)
            .map(|p| p.local.0 as usize)
            .filter(|&p| named[p] && !slot[p])
            .collect();
        let lent = (f.params.iter())
            .filter(|p| p.mode == ParamMode::Borrowed)
            .map(|p| Key::Value(p.local.0 as usize))
            .filter(|k| matches!(k, Key::Value(p) if params.contains(p)))
            .collect();
        let mut lists = Self {
            origin,
            slot,
            named,
            params,
            lent,
            ..Self::default()
        };
        lists.ins = lists.solve(f);
        lists
    }

    /// Whether local `l` is a place that holds a list, whose header the locals hold once it
    /// is assigned.
    pub(crate) fn is_list_place(&self, l: usize) -> bool {
        self.slot[l] && self.named[l]
    }

    /// Starts block `b`, with what every path into it knows.
    pub(crate) fn enter(&mut self, b: usize) {
        self.state = State {
            held: self.ins[b].clone(),
            copies: HashMap::new(),
        };
    }

    /// The place a pointer always points to.
    pub(crate) fn place_of(&self, pointer: &Operand) -> Option<usize> {
        pointer.local().and_then(|l| self.origin[l.0 as usize])
    }

    /// The key of the list an operand holds: the place it was read from, while nothing changed
    /// the place, or the local itself.
    pub(crate) fn key_of(&self, list: &Operand) -> Option<Key> {
        self.key_of_in(&self.state, list)
    }

    /// Whether local `l` lives in memory, a place.
    pub(crate) fn is_place(&self, l: usize) -> bool {
        self.slot[l]
    }

    /// Whether place `p` is the caller's slot that an `inout` parameter, the local `p`, points
    /// to, rather than a local in memory.
    pub(crate) fn is_pointed(&self, p: usize) -> bool {
        !self.slot[p]
    }

    /// Whether the locals hold the header of `key`'s list, and so marks them used.
    pub(crate) fn holds(&mut self, key: Key) -> bool {
        self.used.insert(key);
        self.state.held.contains(&key)
    }

    /// Updates the state across a statement, the emitter's code for it emitted.
    pub(crate) fn step(&mut self, s: &Stmt) {
        let mut state = std::mem::take(&mut self.state);
        self.stmt(&mut state, s);
        self.state = state;
    }

    /// Updates the state across a terminator.
    pub(crate) fn term(&mut self, t: &Terminator) {
        let mut state = std::mem::take(&mut self.state);
        self.terminator(&mut state, t);
        self.state = state;
    }

    fn solve(&self, f: &Function) -> Vec<BTreeSet<Key>> {
        let n = f.blocks.len();
        let mut ins: Vec<Option<BTreeSet<Key>>> = vec![None; n];
        ins[0] = Some(self.params.iter().map(|&p| Key::Value(p)).collect());
        let mut changed = true;
        while changed {
            changed = false;
            for b in 0..n {
                let Some(held) = ins[b].clone() else { continue };
                let mut state = State {
                    held,
                    copies: HashMap::new(),
                };
                for s in &f.blocks[b].stmts {
                    self.stmt(&mut state, s);
                }
                self.terminator(&mut state, &f.blocks[b].term);
                for succ in f.blocks[b].term.successors() {
                    let s = succ.0 as usize;
                    let merged = match &ins[s] {
                        Some(old) => old.intersection(&state.held).copied().collect(),
                        None => state.held.clone(),
                    };
                    if ins[s].as_ref() != Some(&merged) {
                        ins[s] = Some(merged);
                        changed = true;
                    }
                }
            }
        }
        ins.into_iter().map(Option::unwrap_or_default).collect()
    }

    fn stmt(&self, state: &mut State, s: &Stmt) {
        match s {
            Stmt::Assign(d, r) => {
                self.rvalue(state, r);
                let d = d.0 as usize;
                forget_local(state, d, self.slot[d]);
                let read = match r {
                    Rvalue::Use(Operand::Local(p)) if self.slot[p.0 as usize] => Some(p.0 as usize),
                    Rvalue::Load(pointer) => self.place_of(pointer),
                    _ => None,
                };
                if let Some(p) = read
                    && !self.slot[d]
                {
                    state.copies.insert(d, p);
                }
                if self.is_list_place(d) {
                    state.held.insert(Key::Place(d));
                }
            }
            Stmt::Store { slot, .. } => {
                if let Some(p) = self.place_of(slot) {
                    forget_local(state, p, true);
                }
            }
            Stmt::Effect(f, args) => self.effect(state, *f, args),
            Stmt::Drop(l) => forget_local(state, l.0 as usize, self.slot[l.0 as usize]),
            Stmt::ReleaseConstants => forget_all(state, &self.lent),
            Stmt::Dup(_) | Stmt::At(_) | Stmt::Count(..) => {}
        }
    }

    fn rvalue(&self, state: &mut State, r: &Rvalue) {
        let Rvalue::Runtime(f, args) = r else {
            if let Rvalue::FieldSlot { slot, .. } = r
                && let Some(p) = self.place_of(slot)
            {
                forget_local(state, p, true);
            }
            return;
        };
        match f {
            Runtime::ListIndex | Runtime::ListAt | Runtime::ListLen => {
                let list = if *f == Runtime::ListIndex {
                    &args[1]
                } else {
                    &args[0]
                };
                if let Some(k) = self.key_of_in(state, list) {
                    state.held.insert(k);
                }
            }
            Runtime::ListSlot => self.made(state, &args[1]),
            Runtime::ListElement => {
                if let Some(p) = self.place_of(&args[1]) {
                    state.held.insert(Key::Place(p));
                }
            }
            Runtime::ListSlotAt | Runtime::Unique => self.made(state, &args[0]),
            Runtime::ListElementAt => {
                if let Some(p) = self.place_of(&args[0]) {
                    state.held.insert(Key::Place(p));
                }
            }
            _ => self.other(state, *f, args),
        }
    }

    /// Updates the state across any other runtime function: those that make the object a slot
    /// holds unique, which may put a copy in its place, forget the place, and the handlers'
    /// and `when`'s, which run other code of the program between the function's statements,
    /// forget everything. Every other one leaves every list's header as it was, since it
    /// changes no list in place, and the code it calls, such as a key's `hash`, can't reach
    /// one: it reaches a list only through a reference of its own, and a list with two is
    /// copied before a change.
    fn other(&self, state: &mut State, f: Runtime, args: &[Operand]) {
        let slot = match f {
            Runtime::ListPut => args.get(1),
            Runtime::InoutWords => args.first(),
            Runtime::MapStore => args.get(3),
            Runtime::PropStore => args.get(4),
            Runtime::ListAppend | Runtime::Effects(_) | Runtime::Shared(_) => {
                forget_all(state, &self.lent);
                return;
            }
            _ => return,
        };
        match slot.and_then(|s| self.place_of(s)) {
            Some(p) => forget_local(state, p, true),
            None => forget_all(state, &self.lent),
        }
    }

    /// The locals hold the header of the list a place holds, made unique by the statement,
    /// which may have put a copy of it there, which the locals that read the place don't hold.
    fn made(&self, state: &mut State, pointer: &Operand) {
        if let Some(p) = self.place_of(pointer) {
            state.copies.retain(|_, q| *q != p);
            state.held.insert(Key::Place(p));
        }
    }

    /// The locals hold the header of the list a place holds, whose length the statement
    /// changed: the locals of lists held as values are given up, since one may hold this list
    /// without the analysis knowing, but no other place holds it, as it was unique or copied.
    fn resized(&self, state: &mut State, p: usize, copied: bool) {
        state
            .held
            .retain(|k| matches!(k, Key::Place(_)) || self.lent.contains(k));
        if copied {
            state.copies.retain(|_, q| *q != p);
        }
        state.held.insert(Key::Place(p));
    }

    fn effect(&self, state: &mut State, f: Runtime, args: &[Operand]) {
        match f {
            Runtime::Unique => self.made(state, &args[0]),
            Runtime::ListPush => match self.key_of_in(state, &args[0]) {
                Some(Key::Place(p)) if pushed_inline(args) => self.resized(state, p, false),
                // The list nothing else references, which no place holds.
                _ => (state.held).retain(|k| matches!(k, Key::Place(_)) || self.lent.contains(k)),
            },
            _ => self.other(state, f, args),
        }
    }

    fn terminator(&self, state: &mut State, t: &Terminator) {
        let Terminator::Call {
            callee,
            args,
            dest,
            raised,
            ..
        } = t
        else {
            return;
        };
        let operand = |i: usize| match args.get(i) {
            Some(Arg::Borrow(o) | Arg::Ref(o)) => Some(o),
            _ => None,
        };
        match (callee, operand(2)) {
            (Callee::Direct(f), Some(list)) if inline_read(f) || get_size(f, args).is_some() => {
                if let Some(k) = self.key_of_in(state, list) {
                    state.held.insert(k);
                }
            }
            (Callee::Direct(f), Some(slot)) if popped_inline(f, args) => {
                match self.place_of(slot) {
                    Some(p) => self.resized(state, p, true),
                    None => forget_all(state, &self.lent),
                }
            }
            _ => forget_all(state, &self.lent),
        }
        for d in dest.iter().chain(raised.iter().flat_map(|(e, _)| e)) {
            let d = d.0 as usize;
            forget_local(state, d, self.slot[d]);
        }
    }

    fn key_of_in(&self, state: &State, list: &Operand) -> Option<Key> {
        let l = list.local()?.0 as usize;
        if self.slot[l] {
            return Some(Key::Place(l));
        }
        Some(
            state
                .copies
                .get(&l)
                .map_or(Key::Value(l), |&p| Key::Place(p)),
        )
    }
}

/// The natives that read a list and that the code computes inline: its length, and whether it
/// is empty ([`crate::calls`]).
pub(crate) fn inline_read(f: &FnRef) -> bool {
    list_member(f, &["len", "is_empty"])
}

/// The size of the elements of the list that a call of `List.pop` pops, and whether reading
/// one extends its sign, when the code computes it inline: for elements of a constant shape of
/// at most one word.
pub(crate) fn popped_inline(f: &FnRef, args: &[Arg]) -> bool {
    pop_size(f, args).is_some()
}

/// Whether `f` is the standard library's `List.pop`.
pub(crate) fn is_pop(f: &FnRef) -> bool {
    list_member(f, &["pop"])
}

/// Whether a call of `List.pop` pops a list that the compiler's facts prove unique, as the mark
/// of its location says ([`stilt_mir::mir::UNIQUE_LIST`]).
pub(crate) fn popped_unique(args: &[Arg]) -> bool {
    matches!(args.first(), Some(Arg::Borrow(Operand::Const(Const::Word(loc)))) if loc & UNIQUE_LIST != 0)
}

/// See [`popped_inline`].
pub(crate) fn pop_size(f: &FnRef, args: &[Arg]) -> Option<(u64, u8)> {
    if !is_pop(f) {
        return None;
    }
    let Some(Arg::Borrow(o)) = args.get(1) else {
        return None;
    };
    let s = crate::runtime::constant(o).filter(|&s| shape::size(s) <= 8)?;
    Some((
        shape::size(s),
        u8::from(shape::size(s) < 8 && shape::signed(s)),
    ))
}

/// The size of the elements of the list that a call of `List.get` reads, and whether reading
/// one extends its sign, when the code computes it inline: for elements of a constant shape of
/// at most one word that hold no reference, which a read copies as they are.
pub(crate) fn get_size(f: &FnRef, args: &[Arg]) -> Option<(u64, u8)> {
    if !list_member(f, &["get"]) {
        return None;
    }
    let Some(Arg::Borrow(o)) = args.get(1) else {
        return None;
    };
    let s = crate::runtime::constant(o).filter(|&s| shape::size(s) <= 8 && s & shape::HEAP == 0)?;
    Some((
        shape::size(s),
        u8::from(shape::size(s) < 8 && shape::signed(s)),
    ))
}

/// Whether the code appends to a list inline, with the locals of its header: for an element
/// of a constant shape ([`crate::runtime`]).
pub(crate) fn pushed_inline(args: &[Operand]) -> bool {
    args.get(1).and_then(crate::runtime::constant).is_some()
}

fn list_member(f: &FnRef, names: &[&str]) -> bool {
    matches!(f, FnRef::Member(owner, name)
        if &*owner.home == "std.prelude" && &*owner.name == "List" && names.contains(&&**name))
}

/// Forgets what a local held: the list it holds as a value, or as a place, and the copies of
/// the place's list.
fn forget_local(state: &mut State, l: usize, place: bool) {
    state.held.remove(&Key::Value(l));
    state.copies.remove(&l);
    if place {
        state.held.remove(&Key::Place(l));
        state.copies.retain(|_, p| *p != l);
    }
}

fn forget_all(state: &mut State, lent: &BTreeSet<Key>) {
    state.held.retain(|k| lent.contains(k));
    state.copies.clear();
}

#[cfg(test)]
mod tests;
