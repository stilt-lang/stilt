//! The walk of a body in the order of evaluation (facts.analysis-order), which carries the facts
//! from each statement to the next and records what they prove.

use std::collections::{BTreeMap, BTreeSet};

use stilt_hir::hir::{GenericId, LocalId};

use super::dbm::{Key, Term, ZERO};
use super::scan::{Info, Kind, captures, count};
use super::state::State;
use super::values::Value;
use super::{Check, Context, Proof, Proofs};
use crate::tast::walk::Part;
use crate::tast::{Code, Expr, Pat, Stmt, StmtKind, TypedBody};

/// The greatest length of a list and size of an array (facts.greatest-length).
pub(crate) const MAX_LEN: i128 = 1 << 48;

/// The count of facts.large-bodies past which only bounds are kept.
const CAP: usize = 64;

/// A loop being visited: its head terms, the values its head reads, and the states its
/// `continue`s and `break`s take there (facts.loop-heads).
#[derive(Debug, Default)]
pub(crate) struct Frame {
    pub(crate) heads: Vec<Term>,
    pub(crate) bounds: Vec<Term>,
    /// The hidden binding of a `for` over a range's counter, which grows by one on the way back.
    pub(crate) counter: Option<LocalId>,
    pub(crate) continues: Vec<State>,
    pub(crate) breaks: Vec<State>,
    /// Whether it is a loop of the source, which `break` and `continue` reach, rather than a
    /// guard or a spread that facts.match-arms reads as one.
    pub(crate) real: bool,
    /// The visits of loops around it at its push, whose `break`s and `continue`s it takes.
    pub(crate) level: u32,
}

/// The paths of the code of one body being analysed, a closure literal's apart from the body
/// it is written in.
#[derive(Debug, Default)]
pub(crate) struct Paths {
    pub(crate) loops: Vec<Frame>,
    /// The raising paths of each `try … catch` around the code, the innermost last, with the
    /// error its arms handle and the visits of loops at its start, only whose paths reach it.
    pub(crate) catches: Vec<(crate::ty::Ty, u32, Vec<State>)>,
    /// The paths to the end of each `with` around the code, the innermost last, for those whose
    /// handler takes control (facts.paths-that-leave), with the visits of loops at its start.
    pub(crate) withs: Vec<(u32, Option<Vec<State>>)>,
    /// The values the evaluation has read and not yet used (facts.difference-facts).
    pub(crate) held: Vec<Term>,
    pub(crate) capped: bool,
}

pub(crate) struct Walker<'a> {
    pub(crate) cx: &'a Context<'a>,
    pub(crate) info: &'a Info,
    next: Term,
    out: Proofs,
    /// Whether the walk is in a visit of a loop before its last, which proves nothing.
    pub(crate) quiet: u32,
    pub(crate) paths: Paths,
    /// The term of each value parameter in scope (facts.terms).
    pub(crate) values: BTreeMap<GenericId, Term>,
    /// The value parameters' terms with their types' bounds.
    bounded: Vec<(Term, i128, i128)>,
    /// How many terms the facts held when the dead ones were last dropped.
    pub(crate) kept: usize,
}

impl<'a> Walker<'a> {
    pub(crate) fn new(cx: &'a Context<'a>, info: &'a Info) -> Self {
        Self {
            cx,
            info,
            next: ZERO + 1,
            out: Proofs::default(),
            quiet: 0,
            paths: Paths::default(),
            values: BTreeMap::new(),
            bounded: Vec::new(),
            kept: 0,
        }
    }

    /// A term no fact names yet.
    pub(crate) fn fresh(&mut self) -> Term {
        let t = self.next;
        self.next += 1;
        t
    }

    /// A new term of the facts, within `lo` and `hi` where they are given.
    pub(crate) fn term(&mut self, st: &mut State, lo: Option<i128>, hi: Option<i128>) -> Term {
        let t = self.fresh();
        st.facts.add_term(t);
        if let Some(lo) = lo {
            st.facts.assume(ZERO, t, -lo);
        }
        if let Some(hi) = hi {
            st.facts.assume(t, ZERO, hi);
        }
        t
    }

    /// The linear form `t + d`, with its interval from the facts on `t`.
    pub(crate) fn linear(st: &State, t: Term, d: i128) -> Value {
        let (lo, hi) = st.facts.bounds(t);
        Value {
            term: t,
            d,
            linear: true,
            lo: lo.map(|l| l + d),
            hi: hi.map(|h| h + d),
        }
    }

    /// A value that has no linear form: a new term within the interval `(lo, hi)`.
    pub(crate) fn made(&mut self, st: &mut State, (lo, hi): (i128, i128)) -> Value {
        let t = self.term(st, Some(lo), Some(hi));
        Value {
            term: t,
            d: 0,
            linear: false,
            lo: Some(lo),
            hi: Some(hi),
        }
    }

    /// Records whether the check at `at` holds, outside the visits of a loop before its last.
    pub(crate) fn prove(&mut self, at: crate::TextRange, check: Check, holds: bool) {
        if self.quiet > 0 {
            return;
        }
        if holds {
            self.out.proved.push(Proof { at, check });
        } else {
            self.out.unproved.push((at, check));
        }
    }

    /// Analyses a body (facts.verification).
    pub(crate) fn body(&mut self, body: &TypedBody, code: &Code) {
        let params: Vec<LocalId> = body.params.iter().map(|(_, v)| *v).collect();
        let parts = match code {
            Code::Block(b) => vec![Part::Block(b)],
            Code::Expr(e) => vec![Part::Expr(e)],
        };
        let capped = count(self.info, &params, &parts, self.cx.values.len()) > CAP;
        let mut st = State::new(capped);
        self.paths.capped = capped;
        for (id, ty) in &self.cx.values {
            let (lo, hi) = super::values::type_bounds(ty).unwrap_or((i128::MIN, i128::MAX));
            let t = self.fresh();
            self.values.insert(id.clone(), t);
            self.bounded.push((t, lo, hi));
        }
        self.value_terms(&mut st);
        for ((_, v), ty) in body.params.iter().zip(&self.cx.params) {
            self.declare(&mut st, *v);
            self.array_binding(&mut st, ty);
        }
        match code {
            Code::Block(b) => {
                self.block(&mut st, b);
            }
            Code::Expr(e) => {
                self.eval(&mut st, e);
            }
        }
    }

    /// The analysis's findings, once the walk is done.
    pub(crate) fn finish(self) -> Proofs {
        self.out
    }

    /// Gives a binding its first term, length or version, with only its type's bounds (facts.terms
    /// and facts.difference-facts).
    pub(crate) fn declare(&mut self, st: &mut State, v: LocalId) {
        match self.info.kind(v) {
            Kind::Int(lo, hi) => {
                let t = self.term(st, Some(lo), Some(hi));
                st.ints.insert(v, t);
            }
            Kind::List => {
                let t = self.term(st, Some(0), Some(MAX_LEN));
                st.lens.insert(v, t);
                let ver = self.fresh();
                st.vers.insert(v, ver);
            }
            Kind::Map(_) | Kind::Other => {
                let ver = self.fresh();
                st.vers.insert(v, ver);
            }
            Kind::Unbound => {}
        }
    }

    /// An array's size lies within 0 and 2^48 where a binding of its type has a value
    /// (facts.difference-facts).
    pub(crate) fn array_binding(&mut self, st: &mut State, ty: &crate::ty::Ty) {
        if let Some((_, crate::ty::Ty::Param(id))) = ty.arrayed()
            && let Some(&t) = self.values.get(id)
        {
            st.facts.assume(ZERO, t, 0);
            st.facts.assume(t, ZERO, MAX_LEN);
        }
    }

    /// Analyses a closure literal's body, or a handler's operation's, on its own: each capture
    /// has one term with its type's bounds only (facts.verification and facts.terms).
    pub(crate) fn closure(&mut self, params: &[Pat], body: &Expr) {
        let captured = captures(params, body);
        let mut own: Vec<LocalId> = captured.clone();
        for p in params {
            super::scan::patterns(p, &mut |v, _| own.push(v));
        }
        let capped = count(self.info, &own, &[Part::Expr(body)], self.values.len()) > CAP;
        let outer = std::mem::take(&mut self.paths);
        self.paths.capped = capped;
        let mut st = State::new(capped);
        self.value_terms(&mut st);
        for &v in &captured {
            self.declare(&mut st, v);
        }
        for p in params {
            self.bind_pattern(&mut st, p);
        }
        self.eval(&mut st, body);
        self.paths = outer;
    }

    /// Adds the value parameters' terms to a code's first facts, with their types' bounds.
    fn value_terms(&mut self, st: &mut State) {
        for (t, lo, hi) in self.bounded.clone() {
            st.facts.add_term(t);
            st.facts.assume(ZERO, t, -lo);
            st.facts.assume(t, ZERO, hi);
        }
    }

    /// Analyses a block's statements in order, each binding it declares going out of scope at
    /// its end, and gives the value of its last statement.
    pub(crate) fn block(&mut self, st: &mut State, b: &[Stmt]) -> Option<Value> {
        let before = st.bindings();
        let mut last = None;
        for (i, s) in b.iter().enumerate() {
            last = self.stmt(st, s);
            let value = if i + 1 == b.len() { last } else { None };
            self.end_stmt(st, value);
        }
        st.scope_to(&before);
        if !matches!(b.last().map(|s| &s.kind), Some(StmtKind::Expr(_))) {
            last = None;
        }
        last
    }

    /// The end of a statement: every term is dropped that the code after it can't name
    /// (facts.difference-facts), but the statement's value, if it gives one.
    pub(crate) fn end_stmt(&mut self, st: &mut State, value: Option<Value>) {
        if st.is_bottom() {
            return;
        }
        let mut keep: BTreeSet<Term> = self.paths.held.iter().copied().collect();
        keep.extend(self.values.values());
        for f in &self.paths.loops {
            keep.extend(f.heads.iter().chain(&f.bounds));
        }
        keep.extend(value.map(|v| v.term));
        st.drop_terms(&keep);
        self.kept = st.facts.terms().len();
    }

    /// One statement.
    pub(crate) fn stmt(&mut self, st: &mut State, s: &Stmt) -> Option<Value> {
        match &s.kind {
            StmtKind::Let(b) | StmtKind::Var(b) => {
                self.binding(st, b);
                None
            }
            StmtKind::Assign(op, place, value) => {
                self.assign(st, *op, place, value, s.at);
                None
            }
            StmtKind::Assert(c) => {
                self.eval(st, c);
                None
            }
            StmtKind::Yield(place) => {
                self.eval_place(st, place);
                self.lend(st, place);
                None
            }
            StmtKind::Expr(e) => self.eval(st, e),
        }
    }

    /// Keeps `t` while `f` evaluates what follows the value it stands for.
    pub(crate) fn holding<T>(&mut self, held: &[Term], f: impl FnOnce(&mut Self) -> T) -> T {
        let n = self.paths.held.len();
        self.paths.held.extend_from_slice(held);
        let out = f(self);
        self.paths.held.truncate(n);
        out
    }

    /// The presence of keys, kept apart from the facts for the joins (facts.map-keys).
    pub(crate) fn present(st: &State, version: Term, key: &Key) -> bool {
        st.is_bottom() || st.facts.present.contains(&(version, key.clone()))
    }
}
