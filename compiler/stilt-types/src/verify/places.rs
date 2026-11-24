//! Bindings, assignments and places (facts.analysis-order, facts.bindings-and-assignments,
//! facts.proved-indexes and facts.map-keys): the terms, lengths and versions that each gives its
//! binding, and the reads and writes through indexes it proves.

use stilt_hir::hir::{BinaryOp, LocalId};
use stilt_syntax::TextRange;

use super::Check;
use super::dbm::{Key, Term, ZERO};
use super::exprs::bounds_of;
use super::scan::{Kind, patterns};
use super::state::State;
use super::values::Value;
use super::walker::{MAX_LEN, Walker};
use crate::tast::{Binding, Expr, ExprKind, Pat, PatKind};
use crate::ty::Ty;

/// What an index is into: a list binding's length, an array's size, or a map binding's
/// version, or nothing the analysis follows.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Reach {
    Length(Term),
    Size(Size),
    Map(Term),
    Unknown,
}

/// An array's size: a value parameter's term, or a number (facts.terms).
#[derive(Clone, Copy, Debug)]
pub(crate) enum Size {
    Term(Term),
    Number(i128),
}

/// A step of a place whose index has been evaluated, with what it reads.
#[derive(Clone, Debug)]
pub(crate) struct Step {
    pub(crate) at: TextRange,
    /// Whether the container is the place's root binding itself.
    pub(crate) direct: bool,
    /// Whether the container is a map.
    pub(crate) map: bool,
    pub(crate) array: Option<Size>,
    pub(crate) key: Option<Value>,
    pub(crate) map_key: Option<Key>,
}

/// A place, its index expressions evaluated: the binding it is rooted in and its index steps,
/// from the root outward.
#[derive(Clone, Debug, Default)]
pub(crate) struct Place {
    pub(crate) root: Option<LocalId>,
    pub(crate) steps: Vec<Step>,
}

impl Place {
    /// The terms the place's evaluation read, which its use still needs.
    pub(crate) fn held(&self) -> Vec<Term> {
        self.steps
            .iter()
            .flat_map(|s| {
                let key = s.key.map(|v| v.term);
                let form = match &s.map_key {
                    Some(Key::Form(t, _) | Key::Version(t)) => Some(*t),
                    _ => None,
                };
                key.into_iter().chain(form)
            })
            .collect()
    }
}

impl Walker<'_> {
    /// An array's size, if `ty` is an array type whose size the analysis follows.
    pub(crate) fn size(&self, ty: &Ty) -> Option<Size> {
        match ty.arrayed()?.1 {
            Ty::Value(stilt_hir::hir::Value::Int(n)) => Some(Size::Number(*n)),
            Ty::Param(id) => self.values.get(id).map(|t| Size::Term(*t)),
            _ => None,
        }
    }

    /// The key that an expression is, if it is one (facts.map-keys): an integer binding by its
    /// linear form, another binding by its version, or a literal that doesn't interpolate.
    pub(crate) fn key_of(&self, st: &State, k: &Expr) -> Option<Key> {
        match &k.kind {
            ExprKind::Local(v) => match self.info.kind(*v) {
                Kind::Int(..) => st.ints.get(v).map(|t| Key::Form(*t, 0)),
                Kind::Unbound => None,
                _ => st.vers.get(v).map(|t| Key::Version(*t)),
            },
            ExprKind::Str(text) => Some(Key::Text(format!("\"{text}"))),
            ExprKind::Bool(b) => Some(Key::Text(b.to_string())),
            _ => self.number(k).map(|n| Key::Text(n.to_string())),
        }
    }

    /// The map binding an expression names, if its keys can be found again (facts.map-keys).
    pub(crate) fn map_of(&self, st: &State, m: &Expr) -> Option<(LocalId, Term)> {
        let ExprKind::Local(v) = m.kind else {
            return None;
        };
        match self.info.kind(v) {
            Kind::Map(true) => st.vers.get(&v).map(|t| (v, *t)),
            _ => None,
        }
    }

    /// Evaluates the index expressions of a place, in order (values.left-to-right and
    /// values.assignment-order).
    pub(crate) fn eval_place(&mut self, st: &mut State, place: &Expr) -> Place {
        match &place.kind {
            ExprKind::Local(v) => Place {
                root: Some(*v),
                steps: Vec::new(),
            },
            ExprKind::Field(b, _) | ExprKind::TupleField(b, _) => self.eval_place(st, b),
            ExprKind::Index(c, k) => {
                let mut p = self.eval_place(st, c);
                let held = p.held();
                let map_key = self.key_of(st, k);
                let key = self.holding(&held, |w| w.eval(st, k));
                p.steps.push(Step {
                    at: place.at,
                    direct: matches!(c.kind, ExprKind::Local(_)),
                    map: c.ty.is_prelude("Map"),
                    array: self.size(&c.ty),
                    key,
                    map_key,
                });
                p
            }
            _ => {
                // A projection's call, or a value that isn't a place: evaluated as it is.
                self.eval(st, place);
                Place::default()
            }
        }
    }

    /// Checks each index of an evaluated place where its access happens (facts.analysis-order): the
    /// root's first index against its binding's current length or version, and each index into an
    /// array against its size. `store` is set for `m[k] = v`, whose store can't panic.
    pub(crate) fn check_place(&mut self, st: &State, p: &Place, store: bool) {
        for (i, s) in p.steps.iter().enumerate() {
            if store && s.map && i + 1 == p.steps.len() {
                continue;
            }
            let into = match (s.array, s.direct && i == 0, p.root) {
                (Some(size), ..) => Reach::Size(size),
                (None, true, Some(r)) => self.reach_of(st, r),
                _ => Reach::Unknown,
            };
            self.check_index(st, s, into);
        }
    }

    /// What indexing the binding `v` reads, where it is read.
    pub(crate) fn reach_of(&self, st: &State, v: LocalId) -> Reach {
        match self.info.kind(v) {
            Kind::List => st
                .lens
                .get(&v)
                .map_or(Reach::Unknown, |t| Reach::Length(*t)),
            Kind::Map(true) => st.vers.get(&v).map_or(Reach::Unknown, |t| Reach::Map(*t)),
            _ => Reach::Unknown,
        }
    }

    /// Records whether an index step is proved (facts.proved-indexes and facts.map-keys), into what
    /// `into` gives.
    pub(crate) fn check_index(&mut self, st: &State, s: &Step, into: Reach) {
        if s.map {
            let ok = match into {
                Reach::Map(version) => s
                    .map_key
                    .as_ref()
                    .is_some_and(|k| Walker::present(st, version, k)),
                _ => st.is_bottom(),
            };
            self.prove(s.at, Check::MissingKey, ok);
            return;
        }
        let (lower, upper) = Self::in_range(st, s.key, into, true);
        self.prove(s.at, Check::Bounds, lower && upper);
    }

    /// Whether the facts give `0 <= i`, and `i < ℓ`, or `i <= ℓ` when not `strict`, for an
    /// index's value.
    pub(crate) fn in_range(
        st: &State,
        key: Option<Value>,
        into: Reach,
        strict: bool,
    ) -> (bool, bool) {
        let lower = key.is_some_and(|v| st.facts.gives(ZERO, v.term, v.d));
        let slack = if strict { -1 } else { 0 };
        let upper = key.is_some_and(|v| match into {
            Reach::Length(l) | Reach::Size(Size::Term(l)) => st.facts.gives(v.term, l, slack - v.d),
            Reach::Size(Size::Number(n)) => st.facts.gives(v.term, ZERO, n + slack - v.d),
            Reach::Map(..) | Reach::Unknown => st.is_bottom(),
        });
        (lower, upper)
    }

    /// A `let` or a `var` (facts.bindings-and-assignments), or a `let … else`, which is a `match`
    /// of its pattern and the `else` (facts.match-arms).
    pub(crate) fn binding(&mut self, st: &mut State, b: &Binding) {
        let value = self.eval(st, &b.value);
        if let Some(otherwise) = &b.otherwise {
            let held: Vec<Term> = value.iter().map(|v| v.term).collect();
            let fails = self.holding(&held, |w| {
                let mut fails = st.clone();
                w.eval(&mut fails, otherwise);
                fails
            });
            // The `else` leaves: its type is `Never` (patterns.let-else).
            let _ = fails;
            self.match_pattern(st, &b.pattern, value);
            return;
        }
        match &b.pattern.kind {
            PatKind::Bind(v) => self.assign_binding(st, *v, value, &b.value),
            _ => self.match_pattern(st, &b.pattern, value),
        }
    }

    /// `x = e`, for a binding `x`, whose value `e` evaluated to `value`
    /// (facts.bindings-and-assignments).
    pub(crate) fn assign_binding(
        &mut self,
        st: &mut State,
        x: LocalId,
        value: Option<Value>,
        e: &Expr,
    ) {
        match self.info.kind(x) {
            Kind::Int(lo, hi) => self.assign_int(st, x, value, (lo, hi)),
            Kind::List => {
                let len = self.length_of(st, e);
                st.lens.insert(x, len);
                let ver = self.fresh();
                st.vers.insert(x, ver);
            }
            Kind::Map(_) | Kind::Other => {
                let ver = self.fresh();
                st.vers.insert(x, ver);
            }
            Kind::Unbound => {}
        }
        self.array_binding(st, &e.ty);
    }

    /// An integer binding takes a value: the term of a value of facts.linear-forms, or a new term
    /// equal to a linear form, within its type's bounds, non-zero when its interval leaves out zero
    /// or the value is a non-zero term plus 0 (facts.bindings-and-assignments).
    pub(crate) fn assign_int(
        &mut self,
        st: &mut State,
        x: LocalId,
        value: Option<Value>,
        (lo, hi): (i128, i128),
    ) {
        let t = match value {
            Some(v) if !v.linear => v.term,
            Some(v) => {
                let t = self.term(st, None, None);
                st.facts.assume(t, v.term, v.d);
                st.facts.assume(v.term, t, -v.d);
                t
            }
            None => self.term(st, None, None),
        };
        st.facts.assume(ZERO, t, -lo);
        st.facts.assume(t, ZERO, hi);
        let nonzero = value.is_some_and(|v| {
            super::values::leaves_out(v.interval(), 0) || (v.d == 0 && st.facts.is_nonzero(v.term))
        });
        if nonzero {
            st.facts.mark_nonzero(t);
        }
        st.ints.insert(x, t);
    }

    /// The new length a list binding takes from `e` (facts.bindings-and-assignments).
    fn length_of(&mut self, st: &mut State, e: &Expr) -> Term {
        let known = match &e.kind {
            ExprKind::List(es) if !es.iter().any(|x| matches!(x.kind, ExprKind::Spread(_))) => {
                Some((ZERO, i128::try_from(es.len()).unwrap_or(i128::MAX)))
            }
            ExprKind::Local(ys) => st.lens.get(ys).map(|t| (*t, 0)),
            ExprKind::Call(c, _, args, _) => self.made_length(st, c, args),
            _ => None,
        };
        let t = self.term(st, Some(0), Some(MAX_LEN));
        if let Some((u, c)) = known {
            st.facts.assume(t, u, c);
            st.facts.assume(u, t, -c);
        }
        t
    }

    /// The length of `List.new()`, 0, and of `List.repeat(x, n)`, `n`'s value where it is a
    /// linear form proved at least 0.
    fn made_length(
        &self,
        st: &State,
        c: &crate::tast::Callee,
        args: &[crate::tast::Arg],
    ) -> Option<(Term, i128)> {
        let crate::tast::Callee::Member(owner, name) = c else {
            return None;
        };
        if !crate::ty::is_prelude(owner, "List") {
            return None;
        }
        match (&**name, args) {
            ("new", []) => Some((ZERO, 0)),
            ("repeat", [_, n]) => {
                let (t, d) = self.form_of(st, &n.value)?;
                st.facts.gives(ZERO, t, d).then_some((t, d))
            }
            _ => None,
        }
    }

    /// Gives each binding of a pattern a new term, length or version, with its bounds only.
    pub(crate) fn bind_pattern(&mut self, st: &mut State, p: &Pat) {
        let mut bound = Vec::new();
        patterns(p, &mut |v, ty| bound.push((v, ty.clone())));
        for (v, ty) in bound {
            self.declare(st, v);
            self.array_binding(st, &ty);
        }
    }

    /// `place = e` or `place op= e` (values.assignment-order and values.left-to-right;
    /// values.assignment-order and values.compound-assignment-order).
    pub(crate) fn assign(
        &mut self,
        st: &mut State,
        op: Option<BinaryOp>,
        place: &Expr,
        value: &Expr,
        at: TextRange,
    ) {
        if let ExprKind::Local(x) = place.kind {
            let v = self.eval(st, value);
            match (op, self.info.kind(x)) {
                (Some(op), Kind::Int(lo, hi)) => {
                    let Some(old) = st.ints.get(&x).map(|t| Walker::linear(st, *t, 0)) else {
                        return self.assign_int(st, x, None, (lo, hi));
                    };
                    let result = v.map(|v| {
                        let held = [old.term, v.term];
                        self.holding(&held, |w| {
                            w.compound(st, op, (place, old), (value, v), at, (lo, hi))
                        })
                    });
                    self.assign_int(st, x, result, (lo, hi));
                }
                (Some(_), _) => self.havoc(st, x),
                (None, _) => self.assign_binding(st, x, v, value),
            }
            return;
        }
        let p = self.eval_place(st, place);
        let held = p.held();
        let v = self.holding(&held, |w| w.eval(st, value));
        let mut held = held;
        held.extend(v.map(|v| v.term));
        // Only `m[k] = v` itself stores a key, which can't panic (facts.map-keys).
        let stores =
            op.is_none() && matches!(place.kind, ExprKind::Index(..)) && p.steps.len() == 1;
        self.holding(&held, |w| {
            w.check_place(st, &p, stores);
            if let (Some(op), Some(v), Some(ty)) = (op, v, bounds_of(&place.ty)) {
                let old = w.made(st, ty);
                w.compound(st, op, (place, old), (value, v), at, ty);
            }
            w.write_place(st, &p, stores);
        });
    }

    /// `x op v`, the value of a compound assignment, at the statement `at`
    /// (facts.bindings-and-assignments).
    fn compound(
        &mut self,
        st: &mut State,
        op: BinaryOp,
        (place, old): (&Expr, Value),
        (value, v): (&Expr, Value),
        at: TextRange,
        ty: (i128, i128),
    ) -> Value {
        let shown = Expr {
            kind: ExprKind::Error,
            ty: place.ty.clone(),
            at,
        };
        self.arithmetic(st, op, (place, old), (value, v), &shown, ty)
    }

    /// The changes of a write through a place to its root (facts.writes-through-calls and
    /// facts.map-keys): a new version, at which a map's keys stay present, and `k` with them for
    /// `m[k] = v` when `inserts`; a list keeps its length.
    pub(crate) fn write_place(&mut self, st: &mut State, p: &Place, inserts: bool) {
        let Some(root) = p.root else {
            return;
        };
        let Some(&old) = st.vers.get(&root) else {
            return;
        };
        let ver = self.fresh();
        st.vers.insert(root, ver);
        if matches!(self.info.kind(root), Kind::Map(true)) && !p.steps.is_empty() {
            Self::keep_keys(st, old, ver);
            if inserts && let Some(k) = &p.steps[0].map_key {
                st.facts.present.insert((ver, k.clone()));
            }
        }
    }

    /// The keys present at a map's version `old` are present at its new version `new`.
    pub(crate) fn keep_keys(st: &mut State, old: Term, new: Term) {
        let kept: Vec<(Term, Key)> = st
            .facts
            .present
            .iter()
            .filter(|(v, _)| *v == old)
            .map(|(_, k)| (new, k.clone()))
            .collect();
        st.facts.present.extend(kept);
    }

    /// `yield p` lends `p` to the caller (facts.writes-through-calls): its root takes a new term,
    /// length or version, with its bounds only.
    pub(crate) fn lend(&mut self, st: &mut State, place: &Expr) {
        if let Some(root) = super::scan::root(place) {
            self.havoc(st, root);
        }
    }

    /// A binding takes a new term, length and version with only their bounds
    /// (facts.writes-through-calls).
    pub(crate) fn havoc(&mut self, st: &mut State, v: LocalId) {
        if st.ints.contains_key(&v) || st.lens.contains_key(&v) || st.vers.contains_key(&v) {
            self.declare(st, v);
        }
    }
}
