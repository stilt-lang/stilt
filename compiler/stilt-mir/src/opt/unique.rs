//! Making a list unique once (goal debug-speed): a write through an element of a list makes
//! the list unique first, and once the list a place holds is unique, later
//! writes to it need no check, until something can share it again. This pass reads the
//! reference counting that `stilt-rc` inserts, where every new reference to an object is a
//! copy statement (`Stmt::Dup`), so it runs after it.
//!
//! The facts flow forward, a set of places per block, each holding what every path into the
//! block makes true: nothing but the place references the object it holds. Taking an element's
//! slot for a write, appending to the list and storing an element of a type parameter make the
//! place's list unique. A place forgets it when it is given a new value or its value is
//! released, when its value is copied, or a local that may hold its value is, when a call is
//! given a pointer to it, or a value that may be its own, which the callee may keep, and when
//! any runtime function but those that read an element or the length is given such a value.
//! No other code can reach the object: nothing else references it, closures capture by copy
//! (expressions.capture), and only a pointer to it reaches a place (modes.durations and
//! modes.overlapping-inout).
//!
//! A place that is given a new list that nothing else can reference is unique too
//! ([`fresh`]), as `var stack = []` makes `stack`, and popping the list a place holds keeps it
//! unique, since the list stays where it was, or is copied first if something shared it.
//!
//! A loop whose every iteration writes to the list a place holds, and in which nothing can make
//! the place forget that it is unique, makes it unique once, in the block that enters it: the
//! writes inside check nothing, and the list is copied at most once, as the first write would
//! have copied it. Every write the facts prove unique loses its check of the list's count, an
//! append to such a list appends to it where it is, and a making unique that they prove done
//! is removed. These facts hold in every build, so debug builds and release builds check the
//! same counts (builds.same-meaning).

mod fresh;
mod in_place;

pub(crate) use in_place::in_place;

use std::collections::BTreeSet;

use crate::mir::{
    Arg, Callee, Function, Local, LocalDecl, Operand, Repr, Runtime, Rvalue, Stmt, Terminator,
};
use crate::opt::facts::Place;
use crate::opt::loops::{Dominators, Loop, natural_loops};
use crate::opt::places::{Ptr, pointers};
use crate::opt::ranges::reverse_postorder;

/// The places known to hold an object that nothing else references.
type Unique = BTreeSet<Place>;

/// Makes each list unique once, before the loop that writes it, and removes the checks that
/// the facts prove needless.
pub(crate) fn once(f: &mut Function) {
    hoist(f);
    rewrite(f);
}

/// What the analysis knows about a function's locals.
struct Cx {
    ptrs: Vec<Ptr>,
    slot: Vec<bool>,
    /// Whether each local may hold the object that a place holds: read from a place, as the
    /// object it was made unique to or copied from such a local.
    held: Vec<bool>,
    /// Whether each local holds a new list that nothing else can reference.
    fresh: Vec<bool>,
}

impl Cx {
    fn new(f: &Function) -> Self {
        let ptrs = pointers(f);
        let slot: Vec<bool> = f.locals.iter().map(|d| d.slot).collect();
        let held = held(f, &ptrs, &slot);
        let fresh = fresh::fresh(f, &slot);
        Self {
            ptrs,
            slot,
            held,
            fresh,
        }
    }

    fn place(&self, o: &Operand) -> Ptr {
        o.local().map_or(Ptr::Unknown, |l| self.ptrs[l.0 as usize])
    }

    /// Whether the place a pointer points to is known unique.
    fn known(&self, u: &Unique, slot: &Operand) -> bool {
        matches!(self.place(slot), Ptr::Place(p) if u.contains(&p))
    }

    /// Whether an operand may be the object a place holds: a local that lives in memory, which
    /// is a place itself, or one that may hold what a place holds.
    fn holds(&self, o: &Operand) -> bool {
        o.local()
            .is_some_and(|l| self.slot[l.0 as usize] || self.held[l.0 as usize])
    }

    /// Updates `u` across a statement.
    fn stmt(&self, u: &mut Unique, s: &Stmt) {
        match s {
            Stmt::Assign(d, r) => {
                self.rvalue(u, r);
                self.forget_slot(u, *d);
                if let Rvalue::Use(Operand::Local(t)) = r
                    && self.slot[d.0 as usize]
                    && self.fresh.get(t.0 as usize) == Some(&true)
                {
                    u.insert(Place::Slot(*d));
                }
            }
            Stmt::Store { slot, value, .. } => {
                if self.holds(value) {
                    u.clear();
                }
                self.written(u, slot);
            }
            Stmt::Effect(f, args) => self.effect(u, *f, args),
            Stmt::Dup(l) => {
                if self.held[l.0 as usize] {
                    u.clear();
                }
                self.forget_slot(u, *l);
            }
            Stmt::Drop(l) => self.forget_slot(u, *l),
            Stmt::ReleaseConstants => u.clear(),
            Stmt::At(_) | Stmt::Count(..) => {}
        }
    }

    /// Forgets the place that is the slot of `l`, if `l` lives in memory: its value is
    /// replaced, copied or released.
    fn forget_slot(&self, u: &mut Unique, l: Local) {
        if self.slot[l.0 as usize] {
            u.remove(&Place::Slot(l));
        }
    }

    /// Updates `u` across an rvalue: one that makes the object of a place unique, and one that
    /// a value of a place's may reach, which may keep it.
    fn rvalue(&self, u: &mut Unique, r: &Rvalue) {
        match r {
            Rvalue::Runtime(Runtime::ListSlot | Runtime::ListElement, args) => {
                self.made_unique(u, &args[1]);
            }
            Rvalue::Runtime(
                Runtime::ListSlotAt | Runtime::ListElementAt | Runtime::Unique,
                args,
            ) => {
                self.made_unique(u, &args[0]);
            }
            Rvalue::FieldSlot { slot, .. } => self.made_unique(u, slot),
            Rvalue::Runtime(f, args) if !reads_list(*f) && args.iter().any(|a| self.holds(a)) => {
                u.clear();
            }
            Rvalue::Alloc(_, fields) | Rvalue::AllocIn(_, _, fields, _)
                if fields.iter().any(|(o, _)| self.holds(o)) =>
            {
                u.clear();
            }
            _ => {}
        }
    }

    /// Updates `u` across a runtime function called for its effect. An append and a store of
    /// an element of a type parameter make their place's list unique, and a store of a narrow
    /// scalar writes through a pointer into an element; any other may change any place.
    fn effect(&self, u: &mut Unique, f: Runtime, args: &[Operand]) {
        let (slot, rest) = match f {
            Runtime::ListAppend | Runtime::Unique => (args.first(), args.get(1..)),
            Runtime::ListPut => (args.get(1), args.get(2..)),
            Runtime::ListPush | Runtime::StorePacked => (None, Some(args)),
            _ => {
                u.clear();
                return;
            }
        };
        if rest.unwrap_or_default().iter().any(|a| self.holds(a)) {
            u.clear();
        }
        if let Some(s) = slot {
            self.made_unique(u, s);
        }
    }

    fn made_unique(&self, u: &mut Unique, slot: &Operand) {
        if let Ptr::Place(p) = self.place(slot) {
            u.insert(p);
        }
    }

    /// Forgets the place that a write through a pointer reaches.
    fn written(&self, u: &mut Unique, slot: &Operand) {
        match self.place(slot) {
            Ptr::Place(p) => {
                u.remove(&p);
            }
            Ptr::Interior => {}
            Ptr::Unknown => u.clear(),
        }
    }

    /// Updates `u` across a terminator: a call may change what it is given a pointer to, and
    /// keep what it is given, and it defines its results.
    fn term(&self, u: &mut Unique, t: &Terminator) {
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
        // The standard library's `List.len` reads the list it is given and keeps nothing, and
        // its `List.pop` leaves the list it pops where it was, unique once it was.
        let len = matches!(callee, Callee::Direct(f) if crate::opt::is_list_len(f));
        let pop = matches!(callee, Callee::Direct(f) if crate::opt::is_list_pop(f));
        for a in args {
            match a {
                Arg::Ref(_) if pop => {}
                Arg::Ref(p) => self.passed(u, p),
                Arg::Borrow(o) | Arg::Own(o) if !len && self.holds(o) => u.clear(),
                Arg::Lend(words) if !len && words.iter().any(|(o, _)| self.holds(o)) => u.clear(),
                Arg::Borrow(_) | Arg::Own(_) | Arg::Lend(_) => {}
            }
        }
        if let Callee::Value(o) | Callee::Method(o, _) = callee
            && self.holds(o)
        {
            u.clear();
        }
        for &d in dest.iter().chain(raised.iter().flat_map(|(e, _)| e)) {
            self.forget_slot(u, d);
        }
    }

    /// Forgets every word of the value a pointer that a call is given points to, which may span
    /// several words of the same slot or parameter.
    fn passed(&self, u: &mut Unique, p: &Operand) {
        match self.place(p) {
            Ptr::Place(Place::Param(q, _)) => {
                u.retain(|x| !matches!(x, Place::Param(r, _) if *r == q));
            }
            Ptr::Place(Place::Slot(l)) => {
                u.retain(|x| !matches!(x, Place::Slot(m) if m.0 >= l.0));
            }
            Ptr::Interior => {}
            Ptr::Unknown => u.clear(),
        }
    }
}

/// Whether a runtime function only reads a list it is given, keeping no reference to it: an
/// element, read inline or with references of its own, and the length.
fn reads_list(f: Runtime) -> bool {
    matches!(
        f,
        Runtime::ListAt | Runtime::ListIndex | Runtime::ListLen | Runtime::ListGet
    )
}

/// Whether each local of `f` may hold the object a place holds: a word loaded through a
/// pointer that may reach a place, the object a place was made unique to, and a copy of a
/// local that lives in memory or of one that may hold such an object.
fn held(f: &Function, ptrs: &[Ptr], slot: &[bool]) -> Vec<bool> {
    let mut held = vec![false; f.locals.len()];
    let mut changed = true;
    while changed {
        changed = false;
        for stmt in f.blocks.iter().flat_map(|b| &b.stmts) {
            let Stmt::Assign(d, r) = stmt else { continue };
            let reads = match r {
                Rvalue::Load(p) => p
                    .local()
                    .is_none_or(|l| ptrs[l.0 as usize] != Ptr::Interior),
                Rvalue::Use(Operand::Local(s)) => slot[s.0 as usize] || held[s.0 as usize],
                Rvalue::Runtime(Runtime::Unique, _) => true,
                _ => false,
            };
            if reads && !std::mem::replace(&mut held[d.0 as usize], true) {
                changed = true;
            }
        }
    }
    held
}

/// Each block's facts on entry, or `None` for a block that no path reaches.
fn solve(cx: &Cx, f: &Function) -> Vec<Option<Unique>> {
    let mut ins: Vec<Option<Unique>> = vec![None; f.blocks.len()];
    ins[0] = Some(Unique::new());
    let order = reverse_postorder(f);
    let mut changed = true;
    while changed {
        changed = false;
        for &b in &order {
            let Some(mut u) = ins[b].clone() else {
                continue;
            };
            let block = &f.blocks[b];
            for s in &block.stmts {
                cx.stmt(&mut u, s);
            }
            cx.term(&mut u, &block.term);
            for s in block.term.successors() {
                let s = s.0 as usize;
                let merged = match &ins[s] {
                    Some(old) => old.intersection(&u).copied().collect(),
                    None => u.clone(),
                };
                if ins[s].as_ref() != Some(&merged) {
                    ins[s] = Some(merged);
                    changed = true;
                }
            }
        }
    }
    ins
}

/// Replaces each element's slot taken from a list that the facts prove unique by the same
/// slot without the check of the list's count, and removes each making unique they prove done.
fn rewrite(f: &mut Function) {
    let cx = Cx::new(f);
    let ins = solve(&cx, f);
    for (block, u) in f.blocks.iter_mut().zip(ins) {
        let Some(mut u) = u else { continue };
        for mut s in std::mem::take(&mut block.stmts) {
            match &mut s {
                Stmt::Effect(Runtime::Unique, args) if cx.known(&u, &args[0]) => continue,
                Stmt::Assign(_, Rvalue::Runtime(f @ Runtime::ListSlot, args))
                    if cx.known(&u, &args[1]) =>
                {
                    *f = Runtime::ListElement;
                }
                Stmt::Assign(_, Rvalue::Runtime(f @ Runtime::ListSlotAt, args))
                    if cx.known(&u, &args[0]) =>
                {
                    *f = Runtime::ListElementAt;
                }
                _ => {}
            }
            cx.stmt(&mut u, &s);
            block.stmts.push(s);
        }
    }
}

/// Makes each place's list unique before each loop that writes it in every iteration and that
/// nothing in which makes it forget, the innermost loops first, so that an outer loop finds the
/// making unique of the loops it holds.
fn hoist(f: &mut Function) {
    let dom = Dominators::of(f);
    for l in natural_loops(f, &dom) {
        let Some(pre) = l.preheader else { continue };
        let cx = Cx::new(f);
        for p in hoistable(&cx, f, &dom, &l, pre) {
            make_unique_at(f, pre, p);
        }
    }
}

/// The places whose lists a block of the loop that runs in every iteration makes unique, that
/// hold a value where the loop starts, and that nothing in the loop makes forget it.
fn hoistable(cx: &Cx, f: &Function, dom: &Dominators, l: &Loop, pre: usize) -> Vec<Place> {
    let every = |b: usize| l.latches.iter().all(|&latch| dom.dominates(b, latch));
    let mut places: Vec<Place> = Vec::new();
    for &b in l.blocks.iter().filter(|&&b| every(b)) {
        for s in &f.blocks[b].stmts {
            if let Some(Ptr::Place(p)) = made_unique_by(s).map(|o| cx.place(o))
                && !places.contains(&p)
            {
                places.push(p);
            }
        }
    }
    places.retain(|&p| set_before(f, dom, pre, p) && !forgotten_in(cx, f, l, p));
    places
}

/// The pointer to the place whose list a statement makes unique, as a write through an
/// element does.
fn made_unique_by(s: &Stmt) -> Option<&Operand> {
    match s {
        Stmt::Assign(_, Rvalue::Runtime(Runtime::ListSlot, args)) => args.get(1),
        Stmt::Assign(_, Rvalue::Runtime(Runtime::ListSlotAt, args))
        | Stmt::Effect(Runtime::Unique, args) => args.first(),
        _ => None,
    }
}

/// Whether the place holds a value at the end of block `pre`: what an `inout` parameter points
/// to does, and the slot of a local once a block that runs before has assigned it.
fn set_before(f: &Function, dom: &Dominators, pre: usize, p: Place) -> bool {
    let Place::Slot(l) = p else { return true };
    dom.chain(pre).any(|b| {
        f.blocks[b]
            .stmts
            .iter()
            .any(|s| matches!(s, Stmt::Assign(d, _) if *d == l))
    })
}

/// Whether a statement or a terminator of the loop makes the place forget that its list is
/// unique.
fn forgotten_in(cx: &Cx, f: &Function, l: &Loop, p: Place) -> bool {
    let forgets = |step: &dyn Fn(&mut Unique)| {
        let mut u = Unique::from([p]);
        step(&mut u);
        !u.contains(&p)
    };
    l.blocks.iter().any(|&b| {
        let block = &f.blocks[b];
        block.stmts.iter().any(|s| forgets(&|u| cx.stmt(u, s)))
            || forgets(&|u| cx.term(u, &block.term))
    })
}

/// Makes the list of place `p` unique at the end of block `b`, through a pointer to it.
fn make_unique_at(f: &mut Function, b: usize, p: Place) {
    let pointer = match p {
        Place::Param(q, 0) => Operand::Local(q),
        Place::Param(q, words) => new_pointer(f, b, Rvalue::Offset(Operand::Local(q), words)),
        Place::Slot(l) => new_pointer(f, b, Rvalue::SlotOf(l)),
    };
    f.blocks[b]
        .stmts
        .push(Stmt::Effect(Runtime::Unique, vec![pointer]));
}

/// A new local, assigned the pointer `r` at the end of block `b`.
fn new_pointer(f: &mut Function, b: usize, r: Rvalue) -> Operand {
    let l = fresh_local(f);
    f.blocks[b].stmts.push(Stmt::Assign(l, r));
    Operand::Local(l)
}

/// A new local of one word, which counting leaves alone, as a pointer or a borrowed object.
fn fresh_local(f: &mut Function) -> Local {
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
