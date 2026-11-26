//! The reads of `xs[e]` and `m[k]` (facts.analysis-order, facts.proved-indexes and facts.map-keys),
//! and divisions (facts.intervals, facts.proved-divisions and facts.proved-overflow).

use stilt_hir::hir::BinaryOp;

use super::Check;
use super::dbm::{Term, ZERO};
use super::places::{Reach, Step};
use super::state::State;
use super::values::{self, Value, cut, leaves_out};
use super::walker::Walker;
use crate::tast::{Expr, ExprKind};

impl Walker<'_> {
    /// `c[k]` read: the length or version `c` has where it is evaluated, which is before `k`,
    /// against `k`'s value (facts.analysis-order).
    pub(crate) fn index(&mut self, st: &mut State, c: &Expr, k: &Expr, e: &Expr) -> Option<Value> {
        self.eval(st, c);
        let into = match (self.size(&c.ty), &c.kind) {
            (Some(size), _) => Reach::Size(size),
            (None, ExprKind::Local(v)) => self.reach_of(st, *v),
            _ => Reach::Unknown,
        };
        let held: Vec<Term> = match into {
            Reach::Length(t) | Reach::Map(t) => vec![t],
            _ => Vec::new(),
        };
        let map_key = self.key_of(st, k);
        let key = self.holding(&held, |w| w.eval(st, k));
        let step = Step {
            at: e.at,
            direct: true,
            map: c.ty.is_prelude("Map"),
            array: None,
            key,
            map_key,
        };
        // The map's version where `m` was evaluated: `k`'s evaluation can't change it, since
        // a key is a binding or a literal.
        self.check_index(st, &step, into);
        self.opaque(st, &e.ty)
    }

    /// `a / b` and `a % b` on integers: whether the divisor is proved non-zero
    /// (facts.proved-divisions) and a signed division can't overflow (facts.proved-overflow), the
    /// interval of facts.intervals and its relative bounds.
    pub(crate) fn division(
        &mut self,
        st: &mut State,
        op: BinaryOp,
        (dividend, left): (&Expr, Value),
        (divisor, right): (&Expr, Value),
        expr: &Expr,
        ty: (i128, i128),
    ) -> Value {
        let nonzero =
            leaves_out(right.interval(), 0) || (right.d == 0 && st.facts.is_nonzero(right.term));
        self.prove(expr.at, Check::DivideByZero, nonzero);
        // `MIN / -1` and `MIN % -1` overflow.
        if ty.0 < 0 {
            let ok = leaves_out(left.interval(), ty.0) || leaves_out(right.interval(), -1);
            self.prove(expr.at, Check::Overflow, ok);
        }
        // An empty interval, its least above its greatest, is the divisor's in code that can't
        // run, such as the body of a loop over an empty range: nothing bounds the result there.
        let interval = match right.lo {
            Some(bl) if bl >= 1 && right.hi.is_none_or(|bh| bh >= bl) => {
                if op == BinaryOp::Div {
                    values::quotient(left.interval(), bl, right.hi)
                } else {
                    values::remainder(left.interval(), right.hi)
                }
            }
            _ => (None, None),
        };
        let value = self.made(st, cut(interval, ty));
        if op == BinaryOp::Rem
            && st.facts.gives(ZERO, left.term, left.d)
            && let Some((term, offset)) = right.form()
            && st.facts.gives(ZERO, term, offset - 1)
        {
            // `a % b` is less than `b` (facts.relative-bounds).
            st.facts.assume(value.term, term, offset - 1);
        }
        if op == BinaryOp::Div
            && self.number(divisor) == Some(2)
            && let ExprKind::Binary(BinaryOp::Add, l, r) = &dividend.kind
            && let (Some(fl), Some(fr)) = (self.form_of(st, l), self.form_of(st, r))
            && st.facts.gives(ZERO, fl.0, fl.1)
        {
            Self::between(st, value.term, fl, fr);
        }
        value
    }

    /// The middle of `a` and `b`, linear forms with `a ≤ b` proved, lies between them, and
    /// below `b` when `a < b` is proved (facts.relative-bounds).
    pub(crate) fn between(st: &mut State, v: Term, (ta, da): (Term, i128), (tb, db): (Term, i128)) {
        if !st.facts.gives(ta, tb, db - da) {
            return;
        }
        st.facts.assume(ta, v, -da);
        let below = if st.facts.gives(ta, tb, db - da - 1) {
            db - 1
        } else {
            db
        };
        st.facts.assume(v, tb, below);
    }

    /// `a + (b - a) / c`, with `c` a literal of at least 2: the middle of `a` and `b`.
    pub(crate) fn midpoint(&mut self, st: &mut State, a: &Expr, rest: &Expr, v: Term) {
        let ExprKind::Binary(BinaryOp::Div, diff, c) = &rest.kind else {
            return;
        };
        let ExprKind::Binary(BinaryOp::Sub, b, a2) = &diff.kind else {
            return;
        };
        if self.number(c).is_none_or(|c| c < 2) {
            return;
        }
        let (Some(fa), Some(fa2), Some(fb)) = (
            self.form_of(st, a),
            self.form_of(st, a2),
            self.form_of(st, b),
        ) else {
            return;
        };
        if fa == fa2 {
            Self::between(st, v, fa, fb);
        }
    }
}
