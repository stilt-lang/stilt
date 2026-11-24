//! Loops (facts.loop-heads and facts.widening): each loop's head reached by visiting it until its
//! facts stop changing, widened at its thresholds, then narrowed once; the visit from the narrowed
//! facts is the one the body and the exits read.

use std::collections::BTreeSet;

use stilt_hir::hir::LocalId;

use super::dbm::{Facts, Term, ZERO};
use super::scan::{modified, thresholds};
use super::state::{Renamed, Slot, State, meet};
use super::values::Value;
use super::walker::{Frame, Walker};
use crate::tast::walk::Part;
use crate::tast::{Block, Expr, Iterable, Pat, PatKind};

/// What a loop's body is, as its visits read it.
#[derive(Clone, Copy)]
enum Body<'e> {
    While(&'e Expr, &'e Block),
    /// A `for` over a range: its variable, its counter's hidden binding, the second bound's
    /// value, whether the range holds its end, and the body.
    Range(&'e Pat, LocalId, Value, bool, &'e Block),
    Iter(&'e Pat, &'e Block),
    Loop(&'e Block),
    /// An arm's guard, which runs once for each way an or-pattern matches (facts.match-arms).
    Guard(&'e Expr),
    /// A spread's body, evaluated once for each element of its pack.
    Spread(&'e Expr),
}

/// The states a visit of a loop gives: where it leaves, and where it goes back to its head.
#[derive(Default)]
struct Visit {
    exits: Vec<State>,
    back: Vec<State>,
}

/// A loop's head: the term each binding the loop changes takes there, the terms its facts are
/// on, and its thresholds.
struct Head {
    renamed: Vec<(LocalId, Slot, Term)>,
    keep: Vec<Term>,
    versions: BTreeSet<Term>,
    state: State,
    thresholds: Vec<i128>,
    bounds: Vec<Term>,
    counter: Option<LocalId>,
}

/// The hidden binding of the counter of a `for` over a range, at a depth of loops.
fn counter_of(depth: usize) -> LocalId {
    LocalId(u32::MAX - u32::try_from(depth).unwrap_or(0))
}

impl Walker<'_> {
    /// `loop { … }`.
    pub(crate) fn loop_(&mut self, st: &mut State, b: &Block, e: &Expr) -> Option<Value> {
        let code = [Part::Block(b)];
        let v = self.run(st, &code, &[], Body::Loop(b), Vec::new(), None);
        *st = self.join(v.exits);
        self.opaque(st, &e.ty)
    }

    /// `while c { … }`.
    pub(crate) fn while_(&mut self, st: &mut State, c: &Expr, b: &Block) -> Option<Value> {
        let code = [Part::Expr(c), Part::Block(b)];
        let v = self.run(st, &code, &[], Body::While(c, b), Vec::new(), None);
        *st = self.join(v.exits);
        None
    }

    /// `for p in a..b { … }` and `for p in xs { … }` (facts.for-loops).
    pub(crate) fn for_(
        &mut self,
        st: &mut State,
        p: &Pat,
        iterable: &Iterable,
        b: &Block,
        e: &Expr,
    ) -> Option<Value> {
        match iterable {
            Iterable::Range(lo, hi, inclusive) => {
                let first = self.eval(st, lo);
                let held: Vec<Term> = first.iter().map(|v| v.term).collect();
                let second = self.holding(&held, |w| w.eval(st, hi));
                let (Some(first), Some(second)) = (first, second) else {
                    self.havoc_loop(st, &[Part::Block(b)]);
                    return None;
                };
                let counter = counter_of(self.paths.loops.len());
                let start = self.term(st, None, None);
                st.facts.assume(start, first.term, first.d);
                st.facts.assume(first.term, start, -first.d);
                st.ints.insert(counter, start);
                let bounds = vec![first.term, second.term];
                let code = [Part::Expr(lo), Part::Expr(hi), Part::Block(b)];
                let body = Body::Range(p, counter, second, *inclusive, b);
                let v = self.run(st, &code, &[p], body, bounds, Some(counter));
                *st = self.join(v.exits);
                st.ints.remove(&counter);
            }
            Iterable::Iter(source) => {
                self.eval(st, source);
                let code = [Part::Expr(source), Part::Block(b)];
                let v = self.run(st, &code, &[p], Body::Iter(p, b), Vec::new(), None);
                *st = self.join(v.exits);
            }
        }
        self.opaque(st, &e.ty)
    }

    /// An arm's guard when its pattern holds an or-pattern: the body of a loop entered with the
    /// facts after the pattern, whose facts where the guard is true start the arm, and where it
    /// is false the later arms (facts.match-arms).
    pub(crate) fn guard_loop(
        &mut self,
        st: &mut State,
        guard: &Expr,
        pattern: &Pat,
    ) -> (State, State) {
        let code = [Part::Expr(guard)];
        let entry = st.clone();
        let visit = self.visits(
            &entry,
            &code,
            &[pattern],
            Body::Guard(guard),
            Vec::new(),
            None,
        );
        let yes = self.join(visit.exits);
        let no = self.join(visit.back);
        (yes, no)
    }

    /// A spread's body, evaluated once for each element of a pack: a loop.
    pub(crate) fn spread(&mut self, st: &mut State, body: &Expr, _e: &Expr) {
        let code = [Part::Expr(body)];
        let v = self.run(st, &code, &[], Body::Spread(body), Vec::new(), None);
        *st = self.join(v.exits);
    }

    /// Gives every binding a loop's code changes a new term with its bounds only, for a loop
    /// whose bounds have no value the analysis follows.
    fn havoc_loop(&mut self, st: &mut State, code: &[Part<'_>]) {
        for v in modified(code) {
            self.havoc(st, v);
        }
    }

    /// The visits of a loop from `st`, and its final visit's states.
    fn run(
        &mut self,
        st: &State,
        code: &[Part<'_>],
        pats: &[&Pat],
        body: Body<'_>,
        bounds: Vec<Term>,
        counter: Option<LocalId>,
    ) -> Visit {
        self.visits(st, code, pats, body, bounds, counter)
    }

    /// Visits a loop until its head's facts stop changing, then from the narrowed facts, the one
    /// visit that proves anything (facts.loop-heads and facts.widening). Gives that visit, or none
    /// for a loop that is never reached.
    fn visits(
        &mut self,
        entry: &State,
        code: &[Part<'_>],
        pats: &[&Pat],
        body: Body<'_>,
        bounds: Vec<Term>,
        counter: Option<LocalId>,
    ) -> Visit {
        if entry.is_bottom() {
            return Visit::default();
        }
        let head = self.head(entry, code, pats, bounds, counter);
        let mut last = Self::meet_head(&head, entry, &[]).facts;
        self.quiet += 1;
        // The set of the second visit is the first widened; from the sixth visit on, a pair
        // that grew is dropped, whatever the thresholds, which bounds the visits.
        let mut visit = 2;
        let narrowed = loop {
            let mut from = last.clone();
            from.close();
            let v = self.visit(&head, from, body);
            let joined = Self::meet_head(&head, entry, &v.back).facts;
            let thresholds: &[i128] = if visit >= 6 { &[] } else { &head.thresholds };
            let next = last.widen(&joined, thresholds);
            if next.same(&last) {
                break joined;
            }
            last = next;
            visit += 1;
        };
        self.quiet -= 1;
        self.visit(&head, narrowed, body)
    }

    /// The head of a loop entered from `entry`: a new term for each binding the loop's code may
    /// change, and the terms its facts are on (facts.loop-heads).
    fn head(
        &mut self,
        entry: &State,
        code: &[Part<'_>],
        pats: &[&Pat],
        bounds: Vec<Term>,
        counter: Option<LocalId>,
    ) -> Head {
        let mut changed = modified(code);
        changed.extend(counter);
        let mut state = entry.clone();
        let mut renamed = Vec::new();
        for slot in [Slot::Int, Slot::Len, Slot::Ver] {
            let names: Vec<LocalId> = entry
                .slot(slot)
                .keys()
                .filter(|v| changed.contains(v))
                .copied()
                .collect();
            for v in names {
                let h = self.fresh();
                state.slot_mut(slot).insert(v, h);
                renamed.push((v, slot, h));
            }
        }
        let mut keep: BTreeSet<Term> = [ZERO].into_iter().collect();
        keep.extend(state.ints.values().chain(state.lens.values()));
        keep.extend(self.values.values());
        keep.extend(&self.paths.held);
        keep.extend(&bounds);
        for f in &self.paths.loops {
            keep.extend(f.heads.iter().chain(&f.bounds));
        }
        let versions: BTreeSet<Term> = state
            .vers
            .values()
            .chain(&self.paths.held)
            .copied()
            .collect();
        let keep: Vec<Term> = keep
            .into_iter()
            .filter(|t| {
                entry.facts.has(*t) || renamed.iter().any(|(_, s, h)| h == t && *s != Slot::Ver)
            })
            .collect();
        Head {
            renamed,
            keep,
            versions,
            state,
            thresholds: thresholds(self.cx, code, pats),
            bounds,
            counter,
        }
    }

    /// The join of the entry with the paths back to the head, on the head's terms, each head
    /// term read as each path's own (facts.joins and facts.loop-heads).
    fn meet_head(head: &Head, entry: &State, back: &[State]) -> State {
        let paths: Vec<&State> = std::iter::once(entry)
            .chain(back.iter().filter(|s| !s.is_bottom()))
            .collect();
        let mut renamed = Renamed::new();
        for (v, slot, h) in &head.renamed {
            let owns: Vec<Term> = paths
                .iter()
                .map(|p| p.slot(*slot).get(v).copied().unwrap_or(*h))
                .collect();
            renamed.insert(*h, owns);
        }
        let mut facts: Facts = meet(head.keep.clone(), &renamed, &paths);
        let versions = &head.versions;
        let heads: BTreeSet<Term> = head.renamed.iter().map(|(_, _, h)| *h).collect();
        facts
            .present
            .retain(|(v, _)| versions.contains(v) || heads.contains(v));
        let mut out = head.state.clone();
        out.facts = facts;
        out
    }

    /// One visit of a loop's body from the head's facts `from`.
    fn visit(&mut self, head: &Head, from: Facts, body: Body<'_>) -> Visit {
        let mut h = head.state.clone();
        h.facts = from;
        let heads: Vec<Term> = head.renamed.iter().map(|(_, _, t)| *t).collect();
        self.paths.loops.push(Frame {
            heads,
            bounds: head.bounds.clone(),
            counter: head.counter,
            real: !matches!(body, Body::Guard(_) | Body::Spread(_)),
            level: self.quiet,
            ..Frame::default()
        });
        let mut v = self.body_visit(h, body);
        let frame = self.paths.loops.pop().unwrap_or_default();
        v.back.extend(frame.continues);
        v.exits.extend(frame.breaks);
        let scope = head.state.bindings();
        for s in &mut v.exits {
            s.scope_to(&scope);
        }
        v
    }

    fn body_visit(&mut self, mut head: State, body: Body<'_>) -> Visit {
        match body {
            Body::While(cond, block) => {
                let (mut state, exits) = self.cond(&mut head, cond);
                let back = self.block_paths(&mut state, block);
                Visit {
                    exits: vec![exits],
                    back,
                }
            }
            Body::Range(pattern, counter, second, inclusive, block) => {
                self.range_visit(head, pattern, counter, second, inclusive, block)
            }
            Body::Iter(pattern, block) => {
                let mut state = head.clone();
                self.bind_pattern(&mut state, pattern);
                let back = self.block_paths(&mut state, block);
                Visit {
                    exits: vec![head],
                    back,
                }
            }
            Body::Loop(block) => {
                let back = self.block_paths(&mut head, block);
                Visit {
                    exits: Vec::new(),
                    back,
                }
            }
            Body::Guard(g) => {
                let (state, exits) = self.cond(&mut head, g);
                Visit {
                    exits: vec![state],
                    back: vec![exits],
                }
            }
            Body::Spread(e) => {
                let mut state = head.clone();
                self.eval(&mut state, e);
                Visit {
                    exits: vec![head],
                    back: vec![state],
                }
            }
        }
    }

    /// A visit of a `for` over a range: the counter is compared with the second bound at the
    /// head, is the loop's variable in each iteration, within its type's bounds there, and grows
    /// by one at the end of the body (facts.for-loops).
    fn range_visit(
        &mut self,
        head: State,
        pattern: &Pat,
        counter: LocalId,
        second: Value,
        inclusive: bool,
        block: &Block,
    ) -> Visit {
        let Some(&count) = head.ints.get(&counter) else {
            return Visit::default();
        };
        let (mut t, mut f) = (head.clone(), head);
        let slack = if inclusive { 0 } else { -1 };
        t.facts.assume(count, second.term, second.d + slack);
        f.facts.assume(second.term, count, -second.d - slack - 1);
        if let PatKind::Bind(v) = pattern.kind {
            if let super::scan::Kind::Int(lo, hi) = self.info.kind(v) {
                t.facts.assume(ZERO, count, -lo);
                t.facts.assume(count, ZERO, hi);
            }
            t.ints.insert(v, count);
        } else {
            self.bind_pattern(&mut t, pattern);
        }
        let mut back = self.block_paths(&mut t, block);
        for s in &mut back {
            self.step(s, counter);
        }
        Visit {
            exits: vec![f],
            back,
        }
    }

    /// The counter of a `for` over a range grows by one.
    pub(crate) fn step(&mut self, st: &mut State, counter: LocalId) {
        if st.is_bottom() {
            return;
        }
        let Some(&c) = st.ints.get(&counter) else {
            return;
        };
        let next = self.term(st, None, None);
        st.facts.assume(next, c, 1);
        st.facts.assume(c, next, -1);
        st.ints.insert(counter, next);
    }
}
