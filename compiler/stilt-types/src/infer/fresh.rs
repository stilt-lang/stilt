//! The fresh types of shapes (meta.fresh-types): the type of a field, an element or a payload is a
//! rigid type of its own in the arm or the loop body that reads it, its *region*, and no value
//! whose type holds one leaves it: not as the arm's value, assigned or passed `inout` to a
//! variable declared outside, raised, even to a `try` inside it, or returned, nor deciding a type that inference left open
//! outside, each E0351 at the expression.

use std::collections::HashSet;

use stilt_diag::codes;
use stilt_hir::hir::{self, GenericId, LocalId};
use stilt_syntax::TextRange;

use super::{Cx, State};
use crate::tast::{self, ExprKind};
use crate::ty::{Kind, Ty};

/// An arm or a loop body whose fresh types are its own.
pub(super) struct Region {
    ids: Vec<GenericId>,
    /// What it is, as E0351 names it: "arm" or "loop's body".
    what: &'static str,
    /// The variables of the body's types that inference made before it.
    outer_vars: usize,
    /// The locals declared before it.
    outer_locals: HashSet<LocalId>,
    /// Whether a type left open outside it was reported holding one of its fresh types, which
    /// later expressions then needn't be.
    reported: bool,
}

/// The local at the root of a place: a variable, or a field or an element of one.
fn root_local(e: &tast::Expr) -> Option<LocalId> {
    match &e.kind {
        ExprKind::Local(v) => Some(*v),
        ExprKind::Field(base, _) | ExprKind::TupleField(base, _) | ExprKind::Index(base, _) => {
            root_local(base)
        }
        _ => None,
    }
}

impl State<'_> {
    /// A new fresh type, named `letter` in messages, of the region that the next arm or loop
    /// body opens.
    pub(super) fn fresh_type(&mut self, letter: char) -> Ty {
        self.fresh_count += 1;
        let id = GenericId::fresh(self.fresh_count, letter);
        self.fresh_pending.push(id.clone());
        Ty::Param(id)
    }

    /// Forgets the fresh types made since the last region, which a pattern about to be checked
    /// for a region of its own doesn't make.
    pub(super) fn forget_fresh(&mut self) {
        self.fresh_pending.clear();
    }

    /// Opens a region, `what`, for the fresh types made since the last, if any, and tells
    /// whether it opened one.
    pub(super) fn open_region(&mut self, what: &'static str) -> bool {
        if self.fresh_pending.is_empty() {
            return false;
        }
        let ids = std::mem::take(&mut self.fresh_pending);
        self.regions.push(Region {
            ids,
            what,
            outer_vars: self.table.var_count(),
            outer_locals: self.locals.keys().copied().collect(),
            reported: false,
        });
        true
    }

    pub(super) fn close_region(&mut self, opened: bool) {
        if opened {
            self.regions.pop();
        }
    }

    /// The number of regions open, which a function's or a closure's body, or a `try`'s
    /// operand, starts inside.
    pub(super) fn regions_open(&self) -> usize {
        self.regions.len()
    }

    /// The first region, from `depth` on, one of whose fresh types `ty` holds, with that type.
    fn left(&self, ty: &Ty, depth: usize) -> Option<(usize, GenericId)> {
        let frozen = self.table.freeze(ty);
        (depth..self.regions.len()).find_map(|i| {
            self.regions[i]
                .ids
                .iter()
                .find(|g| frozen.holds_fresh(&|h| h == *g))
                .map(|g| (i, g.clone()))
        })
    }

    /// E0351 at `at`, where a value of type `ty` leaves the regions from `depth` on, if its type
    /// holds one of their fresh types; tells whether it does.
    pub(super) fn leaving(&mut self, at: TextRange, ty: &Ty, depth: usize, how: &str) -> bool {
        let Some((i, g)) = self.left(ty, depth) else {
            return false;
        };
        self.report_leaving(at, i, &g, how);
        true
    }

    fn report_leaving(&mut self, at: TextRange, region: usize, g: &GenericId, how: &str) {
        let what = self.regions[region].what;
        self.regions[region].reported = true;
        let name = (self.env.names)(g);
        let message = format!(
            "this value's type holds `{name}`, a fresh type of this {what}, so it can't {how}"
        );
        self.error(codes::E0351, at, message);
    }

    /// The first region a variable is declared outside of, or the number of regions open when
    /// it is declared in all of them.
    fn depth_of(&self, local: LocalId) -> usize {
        self.regions
            .iter()
            .position(|r| r.outer_locals.contains(&local))
            .unwrap_or(self.regions.len())
    }

    /// The first region that a place's variable is declared outside of, if any.
    pub(super) fn place_depth(&self, place: &tast::Expr) -> usize {
        root_local(place).map_or(self.regions.len(), |v| self.depth_of(v))
    }

    /// Checks `e` against `expected`, where its value leaves the regions from `depth` on: E0351
    /// rather than a mismatch when its type holds one of their fresh types and `expected` is open.
    /// Against a type already known outside, a fresh type is a mismatch, E0311 (meta.leaving-arm).
    pub(super) fn check_leaving(
        &mut self,
        cx: &mut Cx,
        (expected, depth, how): (&Ty, usize, &str),
        e: &hir::Expr,
    ) -> tast::Expr {
        if depth >= self.regions.len() || !self.holds_open(expected) {
            return self.check(cx, expected, e);
        }
        let v = self.infer(cx, Some(expected), e);
        if !self.leaving(e.at, &v.ty, depth, how) {
            self.fits(e.at, expected, &v.ty);
        }
        v
    }

    /// Whether `ty` holds a type that inference left open, which a value of any type could decide.
    /// A literal's type is a number type already (numbers.integer-literals and
    /// numbers.float-literals), so it is known.
    fn holds_open(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Var(_) => match self.table.unsolved(ty) {
                Some(v) => v.kind == Kind::Any,
                None => self.holds_open(&self.table.freeze(ty)),
            },
            Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().any(|t| self.holds_open(t)),
            Ty::App(head, ts) => self.holds_open(head) || ts.iter().any(|t| self.holds_open(t)),
            Ty::Fn(f) => {
                f.params.iter().any(|(_, t)| self.holds_open(t))
                    || self.holds_open(&f.ret)
                    || f.row.raise.as_deref().is_some_and(|t| self.holds_open(t))
            }
            Ty::Spread(s) => self.holds_open(&s.elem),
            Ty::Handler(_) | Ty::Param(_) | Ty::SelfTy | Ty::Value(_) | Ty::Error => false,
        }
    }

    /// E0351 at `at` where the expression there made a type that inference left open outside a
    /// region hold one of its fresh types, once per region.
    pub(super) fn escaped(&mut self, at: TextRange) {
        for i in (0..self.regions.len()).rev() {
            let r = &self.regions[i];
            if r.reported {
                continue;
            }
            let found = (0..r.outer_vars).find_map(|v| {
                let t = self.table.freeze(&self.table.var(v));
                r.ids.iter().find(|g| t.holds_fresh(&|h| h == *g)).cloned()
            });
            if let Some(g) = found {
                self.report_leaving(at, i, &g, "decide a type that is open outside it");
            }
        }
    }

    /// The value of an arm whose region is the innermost: E0351 when its type holds one of the
    /// region's fresh types and no type known outside the arm rejected it (meta.leaving-arm).
    pub(super) fn arm_value(&mut self, body: &tast::Expr, expected: Option<&Ty>) {
        let depth = self.regions.len() - 1;
        if self.regions[depth].reported {
            return;
        }
        let known = expected.is_some_and(|t| self.left(t, depth).is_none());
        if !known {
            self.leaving(body.at, &body.ty, depth, "be the value of the arm");
        }
    }

    /// The regions that `return` leaves, for a context that starts here.
    pub(super) fn enter_regions(&self, inner: &mut Cx) {
        inner.returns_at = self.regions.len();
    }
}
