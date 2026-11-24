//! Range facts: what each statement of a function makes true of its integers and its lists,
//! from which checks are discharged.
//!
//! The facts flow forward, a set per block, from the entry to a fixed point, each block's set
//! holding what every path into it makes true ([`Facts`]). A loop counter gets its facts this
//! way: `i` of `for i in 0..n` is at least 0, because it starts at 0 and steps by 1 below `n`,
//! and is below `n` where the loop's test has held. A list's length is known where the list was
//! measured, and stays known while nothing can change it: a list a local holds can't change
//! while the local holds it, since every change makes its object unique first, save a push
//! onto a list that lowering is building, which changes no other list, as nothing else
//! references it; and what a place holds changes only through a store to it, an element
//! appended to it, or a call given a pointer to it (modes.durations and modes.overlapping-inout).

use crate::mir::{
    Arg, Block, Callee, Const, Function, Local, NumKind, Operand, Prim, Repr, Runtime, Rvalue,
    Stmt, Terminator,
};
use crate::opt::arith::{add_fits, bounds, difference, mul_fits, sub_fits, sum, zero_extended};
use crate::opt::facts::{Fact, Facts, Holder, Place, Rel, Term};
use crate::opt::places::{Ptr, pointers};

/// The local an assignment defines, standing for its new value while the facts of the
/// assignment are made from those that held before it, which may name its old one.
const RESULT: Local = Local(u32::MAX);

/// What the analysis of one function knows about its locals.
pub(crate) struct Cx {
    /// Where each pointer points.
    ptrs: Vec<Ptr>,
    /// Whether each local lives in memory, where a pointer can change it.
    slot: Vec<bool>,
    /// Whether each local holds a scalar.
    scalar: Vec<bool>,
}

impl Cx {
    pub(crate) fn new(f: &Function) -> Self {
        Self {
            ptrs: pointers(f),
            slot: f.locals.iter().map(|d| d.slot).collect(),
            scalar: f.locals.iter().map(|d| d.repr == Repr::Scalar).collect(),
        }
    }

    /// The integer an operand is, if facts can name it: a constant, or a local that only
    /// assignments change.
    pub(crate) fn term(&self, o: &Operand) -> Option<Term> {
        match o {
            Operand::Local(l) if !self.slot[l.0 as usize] => Some(Term::Local(*l)),
            Operand::Const(Const::Word(w)) => Some(Term::Const(w.cast_signed())),
            Operand::Local(_) | Operand::Const(_) => None,
        }
    }

    fn place(&self, o: &Operand) -> Ptr {
        o.local().map_or(Ptr::Unknown, |l| self.ptrs[l.0 as usize])
    }

    /// The place a pointer points to, if it points to one rather than into an object.
    pub(crate) fn place_of(&self, o: &Operand) -> Option<Place> {
        match self.place(o) {
            Ptr::Place(p) => Some(p),
            Ptr::Interior | Ptr::Unknown => None,
        }
    }

    /// Updates `facts` across a statement.
    pub(crate) fn stmt(&self, facts: &mut Facts, s: &Stmt) {
        match s {
            Stmt::Assign(d, r) => {
                let made = self.made(facts, *d, r);
                self.rvalue_effects(facts, r);
                self.redefine(facts, *d);
                for f in made {
                    facts.insert(f);
                }
            }
            Stmt::Store { slot, .. } => written(facts, self.place(slot)),
            Stmt::Effect(f, args) => self.effect(facts, *f, args),
            Stmt::ReleaseConstants => facts.kill_places(|_| true),
            Stmt::Dup(_) | Stmt::Drop(_) | Stmt::At(_) | Stmt::Count(..) => {}
        }
        facts.bound();
    }

    /// Forgets what depends on the value of `d`, which is given a new one.
    fn redefine(&self, facts: &mut Facts, d: Local) {
        facts.kill_local(d);
        if self.slot[d.0 as usize] {
            facts.kill_places(|p| p == Place::Slot(d));
        }
    }

    /// Forgets what memory an rvalue may write held: it may make the object of a slot unique.
    fn rvalue_effects(&self, facts: &mut Facts, r: &Rvalue) {
        let slot = match r {
            Rvalue::FieldSlot { slot, .. } => slot,
            Rvalue::Runtime(Runtime::Unique | Runtime::ListSlotAt, args) => &args[0],
            Rvalue::Runtime(Runtime::ListSlot, args) => &args[1],
            _ => return,
        };
        made_unique(facts, self.place(slot));
    }

    /// Forgets what a runtime function called for its effect may change. A list pushed onto
    /// grows, and nothing else references it, as lowering pushes only onto a list it is
    /// building: what holds that list forgets its length, and every other list keeps its own.
    /// An element appended to the list a place holds changes the place. An element stored in a
    /// list makes the list unique, and a store through a pointer into an element, whose list
    /// was made unique when the pointer was taken, changes no place.
    fn effect(&self, facts: &mut Facts, f: Runtime, args: &[Operand]) {
        let at = |i: usize| args.get(i).map_or(Ptr::Unknown, |o| self.place(o));
        match f {
            Runtime::ListPush => match args.first() {
                Some(Operand::Local(l)) => {
                    let mut list = vec![Holder::Local(*l)];
                    if self.slot[l.0 as usize] {
                        list.push(Holder::Place(Place::Slot(*l)));
                    }
                    let held = facts.sharers(list);
                    facts.kill_lengths_of(&held);
                }
                _ => facts.kill_lengths(),
            },
            Runtime::ListAppend | Runtime::StorePacked => written(facts, at(0)),
            Runtime::ListPut => made_unique(facts, at(1)),
            Runtime::MapStore => written(facts, at(3)),
            Runtime::PropStore => written(facts, at(4)),
            _ => facts.kill_places(|_| true),
        }
    }

    /// The facts that assigning `r` to `d` makes true, from those that held before. A local
    /// that lives in memory has none: a pointer can change it.
    fn made(&self, facts: &Facts, d: Local, r: &Rvalue) -> Vec<Fact> {
        if self.slot[d.0 as usize] {
            return Vec::new();
        }
        let mut out = Vec::new();
        match r {
            Rvalue::Use(o) => self.copied(facts, o, &mut out),
            Rvalue::Load(p) => {
                if let Ptr::Place(at) = self.place(p) {
                    out.push(Fact::Holds(RESULT, at));
                }
            }
            Rvalue::Prim(p, args, _) => self.computed(facts, *p, args, &mut out),
            Rvalue::Runtime(f, args) => self.measured(facts, *f, args, &mut out),
            _ => {}
        }
        out.into_iter()
            .filter(|f| !f.mentions(d))
            .map(|f| f.map(&|l| if l == RESULT { d } else { l }))
            .collect()
    }

    /// The facts of a copy of `o`: each fact about `o`, about the copy, and which place the
    /// copy holds the word of when `o` lives in memory.
    fn copied(&self, facts: &Facts, o: &Operand, out: &mut Vec<Fact>) {
        match o {
            Operand::Local(s) if self.slot[s.0 as usize] => {
                out.push(Fact::Holds(RESULT, Place::Slot(*s)));
            }
            Operand::Local(s) => {
                out.extend(
                    facts
                        .iter()
                        .filter(|f| f.mentions(*s))
                        .map(|f| f.map(&|l| if l == *s { RESULT } else { l })),
                );
                // The copy equals its source while neither changes, which a later test of one
                // tells of the other.
                if self.scalar[s.0 as usize] {
                    let (s, r) = (Term::Local(*s), Term::Local(RESULT));
                    out.extend([Fact::Rel(Rel::Le(r, s)), Fact::Rel(Rel::Le(s, r))]);
                }
            }
            Operand::Const(Const::Word(w)) => {
                let (c, r) = (Term::Const(w.cast_signed()), Term::Local(RESULT));
                out.extend([Fact::Rel(Rel::Le(c, r)), Fact::Rel(Rel::Le(r, c))]);
            }
            Operand::Const(_) => {}
        }
    }

    /// The facts of a list's length, and of an element read or an element's slot taken: an
    /// index that didn't panic was in bounds.
    fn measured(&self, facts: &Facts, f: Runtime, args: &[Operand], out: &mut Vec<Fact>) {
        let in_bounds = |l: &Local, i: &Operand, out: &mut Vec<Fact>| {
            if let Some(i) = self.term(i) {
                out.extend(facts.holders(*l).into_iter().map(|h| Fact::InBounds(i, h)));
            }
        };
        match (f, args) {
            (Runtime::ListLen, [Operand::Local(l)]) => {
                out.extend(facts.holders(*l).into_iter().map(|h| Fact::Len(RESULT, h)));
                out.push(Fact::Rel(Rel::Le(Term::Const(0), Term::Local(RESULT))));
            }
            (Runtime::ListIndex, [_, Operand::Local(l), i, elem, ..])
            | (Runtime::ListAt, [Operand::Local(l), i, elem, ..]) => {
                in_bounds(l, i, out);
                if zero_extended(elem) {
                    out.push(Fact::Rel(Rel::Le(Term::Const(0), Term::Local(RESULT))));
                }
            }
            (Runtime::ListGet, [_, Operand::Local(l), i, ..]) => in_bounds(l, i, out),
            (Runtime::ListSlot, [_, slot, i, ..]) | (Runtime::ListSlotAt, [slot, i, ..]) => {
                if let (Some(p), Some(i)) = (self.place_of(slot), self.term(i)) {
                    out.push(Fact::InBounds(i, Holder::Place(p)));
                }
            }
            _ => {}
        }
    }

    /// The facts of a primitive operation's result.
    fn computed(&self, facts: &Facts, op: Prim, args: &[Operand], out: &mut Vec<Fact>) {
        let terms: Vec<Option<Term>> = args.iter().map(|a| self.term(a)).collect();
        let (result, zero) = (Term::Local(RESULT), Term::Const(0));
        let (lhs, rhs) = match terms.as_slice() {
            [Some(lhs), Some(rhs)] => (*lhs, *rhs),
            [Some(Term::Local(cond))] if op == Prim::BoolNot => {
                out.extend(facts.iter().filter_map(|f| match f {
                    Fact::Cond(local, rel) if local == *cond => {
                        Some(Fact::Cond(RESULT, rel.negated()))
                    }
                    _ => None,
                }));
                return;
            }
            _ => return,
        };
        let both_nonneg = facts.nonneg(lhs) && facts.nonneg(rhs);
        match op {
            Prim::Lt(NumKind::I64) => out.push(Fact::Cond(RESULT, Rel::Lt(lhs, rhs))),
            Prim::Le(NumKind::I64) => out.push(Fact::Cond(RESULT, Rel::Le(lhs, rhs))),
            Prim::Add(NumKind::I64) | Prim::AddUp(NumKind::I64) => {
                sum(facts, result, lhs, rhs, out);
                bounds(facts, (result, lhs, rhs), |a, b| a + b, out);
            }
            Prim::AddWrap(NumKind::I64) if add_fits(facts, lhs, rhs) => {
                sum(facts, result, lhs, rhs, out);
                bounds(facts, (result, lhs, rhs), |a, b| a + b, out);
            }
            Prim::Sub(NumKind::I64) => {
                difference(facts, result, lhs, rhs, out);
                bounds(facts, (result, lhs, rhs), |a, b| a - b, out);
            }
            Prim::SubWrap(NumKind::I64) if sub_fits(facts, lhs, rhs) => {
                difference(facts, result, lhs, rhs, out);
                bounds(facts, (result, lhs, rhs), |a, b| a - b, out);
            }
            Prim::Mul(NumKind::I64) => {
                if both_nonneg {
                    out.push(Fact::Rel(Rel::Le(zero, result)));
                }
                bounds(facts, (result, lhs, rhs), |a, b| a * b, out);
            }
            Prim::MulWrap(NumKind::I64) if mul_fits(facts, lhs, rhs) => {
                bounds(facts, (result, lhs, rhs), |a, b| a * b, out);
            }
            Prim::Div(NumKind::I64) | Prim::DivByPositive(NumKind::I64) if both_nonneg => {
                out.extend([Rel::Le(zero, result), Rel::Le(result, lhs)].map(Fact::Rel));
            }
            Prim::Rem(NumKind::I64) | Prim::RemByPositive(NumKind::I64) if both_nonneg => {
                out.extend([Rel::Le(zero, result), Rel::Lt(result, rhs)].map(Fact::Rel));
            }
            _ => {}
        }
    }

    /// The facts on each edge out of a block whose statements leave `facts`: what a branch
    /// tests, and what a call defines or may write.
    pub(crate) fn edges(&self, t: &Terminator, mut facts: Facts) -> Vec<(usize, Facts)> {
        match t {
            Terminator::Branch {
                cond: Operand::Local(c),
                then,
                otherwise,
            } => {
                let tested: Vec<Rel> = facts
                    .iter()
                    .filter_map(|f| match f {
                        Fact::Cond(m, r) if m == *c => Some(r),
                        _ => None,
                    })
                    .collect();
                let (mut yes, mut no) = (facts.clone(), facts);
                for r in tested {
                    yes.insert(Fact::Rel(r));
                    no.insert(Fact::Rel(r.negated()));
                }
                vec![(then.0 as usize, yes), (otherwise.0 as usize, no)]
            }
            Terminator::Call {
                callee,
                args,
                dest,
                next,
                raised,
            } => {
                for a in args {
                    if let Arg::Ref(p) = a {
                        passed(&mut facts, self.place(p));
                    }
                }
                let mut out = Vec::new();
                if let Some((error, at)) = raised {
                    let mut e = facts.clone();
                    for l in error {
                        self.redefine(&mut e, *l);
                    }
                    out.push((at.0 as usize, e));
                }
                let made = length_of(callee, args, dest, &facts);
                for l in dest {
                    self.redefine(&mut facts, *l);
                }
                for f in made {
                    facts.insert(f);
                }
                out.push((next.0 as usize, facts));
                out
            }
            _ => t
                .successors()
                .into_iter()
                .map(|s| (s.0 as usize, facts.clone()))
                .collect(),
        }
    }
}

/// Forgets what a place that a write through a pointer reaches held.
fn written(facts: &mut Facts, at: Ptr) {
    match at {
        Ptr::Place(p) => facts.kill_places(|q| q == p),
        Ptr::Interior => {}
        Ptr::Unknown => facts.kill_places(|_| true),
    }
}

/// Forgets which locals hold the same word as the place a pointer reaches, whose object is made
/// unique: copy-on-write gives the place a copy, of the same length if it is a list.
fn made_unique(facts: &mut Facts, at: Ptr) {
    match at {
        Ptr::Place(p) => facts.kill_holds(|q| q == p),
        Ptr::Interior => {}
        Ptr::Unknown => facts.kill_holds(|_| true),
    }
}

/// Forgets what a callee given a pointer may change: every word of the value it points to,
/// which may span several words of the same slot or parameter.
fn passed(facts: &mut Facts, at: Ptr) {
    match at {
        Ptr::Place(Place::Param(p, _)) => {
            facts.kill_places(|q| matches!(q, Place::Param(r, _) if r == p));
        }
        Ptr::Place(Place::Slot(l)) => facts.kill_places(|q| match q {
            Place::Slot(m) => m.0 >= l.0,
            Place::Param(..) => false,
        }),
        Ptr::Interior => {}
        Ptr::Unknown => facts.kill_places(|_| true),
    }
}

/// The facts of a call to the standard library's `List.len`, a native that takes the list
/// last: its result is the length of what holds the list, and at least 0.
fn length_of(callee: &Callee, args: &[Arg], dest: &[Local], facts: &Facts) -> Vec<Fact> {
    let (Callee::Direct(f), Some(Arg::Borrow(Operand::Local(list))), [n]) =
        (callee, args.last(), dest)
    else {
        return Vec::new();
    };
    if !crate::opt::is_list_len(f) {
        return Vec::new();
    }
    let mut out: Vec<Fact> = facts
        .holders(*list)
        .into_iter()
        .map(|h| Fact::Len(*n, h))
        .collect();
    out.push(Fact::Rel(Rel::Le(Term::Const(0), Term::Local(*n))));
    out
}

/// Each block's facts on entry, or `None` for a block no path reaches or when the analysis
/// gives up, as it does past a bound on its work.
pub(crate) fn solve(cx: &Cx, f: &Function) -> Option<Vec<Option<Facts>>> {
    let n = f.blocks.len();
    let mut ins: Vec<Option<Facts>> = vec![None; n];
    ins[0] = Some(Facts::default());
    let order = reverse_postorder(f);
    let mut budget = 16 * n + 64;
    loop {
        let mut changed = false;
        for &b in &order {
            let Some(mut facts) = ins[b].clone() else {
                continue;
            };
            let block: &Block = &f.blocks[b];
            for s in &block.stmts {
                cx.stmt(&mut facts, s);
            }
            for (s, out) in cx.edges(&block.term, facts) {
                if let Some(old) = &mut ins[s] {
                    changed |= old.meet(&out);
                } else {
                    ins[s] = Some(out);
                    changed = true;
                }
            }
            budget = budget.checked_sub(1)?;
        }
        if !changed {
            return Some(ins);
        }
    }
}

/// The blocks that the entry reaches, each before its successors except along back edges.
pub(crate) fn reverse_postorder(f: &Function) -> Vec<usize> {
    let mut seen = vec![false; f.blocks.len()];
    let mut post = Vec::with_capacity(f.blocks.len());
    // Each block being visited, with how many of its successors it has followed.
    let mut stack = vec![(0usize, 0usize)];
    seen[0] = true;
    while let Some(&(b, next)) = stack.last() {
        let succs = f.blocks[b].term.successors();
        let Some(s) = succs.get(next) else {
            post.push(b);
            stack.pop();
            continue;
        };
        stack.last_mut().expect("a block is being visited").1 += 1;
        let s = s.0 as usize;
        if !std::mem::replace(&mut seen[s], true) {
            stack.push((s, 0));
        }
    }
    post.reverse();
    post
}
