//! Conditions (facts.conditions): the facts a condition gives where it is true and where it is
//! false, in an `if`, an `else if`, a `while`'s head and a `match` arm's guard.

use stilt_hir::hir::{BinaryOp, UnaryOp};

use super::dbm::ZERO;
use super::scan::Kind;
use super::state::State;
use super::values::Value;
use super::walker::Walker;
use crate::tast::{Callee, Expr, ExprKind};
use crate::ty::is_prelude;

/// A comparison of two integers, `a < b` or `a <= b`, read with its sides in that order.
#[derive(Clone, Copy, Debug)]
struct Order {
    a: (u32, i128),
    b: (u32, i128),
    strict: bool,
}

impl Order {
    /// The order of `a op b`, for `op` one of `<`, `<=`, `>` and `>=`.
    fn of(op: BinaryOp, a: (u32, i128), b: (u32, i128)) -> Option<Self> {
        match op {
            BinaryOp::Lt => Some(Self { a, b, strict: true }),
            BinaryOp::Le => Some(Self {
                a,
                b,
                strict: false,
            }),
            BinaryOp::Gt => Some(Self {
                a: b,
                b: a,
                strict: true,
            }),
            BinaryOp::Ge => Some(Self {
                a: b,
                b: a,
                strict: false,
            }),
            _ => None,
        }
    }

    /// Where it is false: `b <= a`, or `b < a` for `<=`.
    fn negated(self) -> Self {
        Self {
            a: self.b,
            b: self.a,
            strict: !self.strict,
        }
    }

    /// Adds the fact it states: `a − b ≤ −1`, or `≤ 0`.
    fn assume(self, st: &mut State) {
        let ((ta, da), (tb, db)) = (self.a, self.b);
        let slack = if self.strict { -1 } else { 0 };
        st.facts.assume(ta, tb, db - da + slack);
    }
}

impl Walker<'_> {
    /// Evaluates a condition, and gives the states where it is true and where it is false.
    pub(crate) fn cond(&mut self, st: &mut State, expr: &Expr) -> (State, State) {
        match &expr.kind {
            ExprKind::Unary(UnaryOp::Not, inner) if expr.ty.is_prelude("bool") => {
                let (yes, no) = self.cond(st, inner);
                (no, yes)
            }
            ExprKind::Binary(BinaryOp::And, left, right) => {
                let (at, af) = self.cond(st, left);
                let mut at = at;
                let (bt, bf) = self.cond(&mut at, right);
                let no = self.join(vec![af, bf]);
                (bt, no)
            }
            ExprKind::Binary(BinaryOp::Or, left, right) => {
                let (at, af) = self.cond(st, left);
                let mut af = af;
                let (bt, bf) = self.cond(&mut af, right);
                let yes = self.join(vec![at, bt]);
                (yes, bf)
            }
            ExprKind::Binary(op, left, right) if left.ty.integer_name().is_some() => {
                let lhs = self.eval(st, left);
                let held: Vec<_> = lhs.iter().map(|value| value.term).collect();
                let rhs = self.holding(&held, |w| w.eval(st, right));
                Self::compare(st, *op, (left, lhs), (right, rhs))
            }
            ExprKind::Call(Callee::Member(owner, name), _, args, _) => {
                let _ = self.call(st, expr);
                self.called(st, owner, name, args)
            }
            _ => {
                self.eval(st, expr);
                (st.clone(), st.clone())
            }
        }
    }

    /// The facts of `a op b` on integers whose values are `x` and `y`.
    fn compare(
        st: &State,
        op: BinaryOp,
        (left, lhs): (&Expr, Option<Value>),
        (right, rhs): (&Expr, Option<Value>),
    ) -> (State, State) {
        let (mut yes, mut no) = (st.clone(), st.clone());
        let (Some(fx), Some(fy)) = (
            lhs.and_then(|value| value.form()),
            rhs.and_then(|value| value.form()),
        ) else {
            return (yes, no);
        };
        match op {
            BinaryOp::Eq | BinaryOp::Ne => {
                let (same, differ) = if op == BinaryOp::Eq {
                    (&mut yes, &mut no)
                } else {
                    (&mut no, &mut yes)
                };
                if let Some(order) = Order::of(BinaryOp::Le, fx, fy) {
                    order.assume(same);
                }
                if let Some(order) = Order::of(BinaryOp::Ge, fx, fy) {
                    order.assume(same);
                }
                if let Some(term) = Self::against_zero((left, fx), (right, fy)) {
                    differ.facts.mark_nonzero(term);
                }
            }
            _ => {
                if let Some(order) = Order::of(op, fx, fy) {
                    order.assume(&mut yes);
                    order.negated().assume(&mut no);
                }
            }
        }
        (yes, no)
    }

    /// The term `t` of `t + 0` compared with the literal 0, in either order (facts.conditions).
    fn against_zero((a, fa): (&Expr, (u32, i128)), (b, fb): (&Expr, (u32, i128))) -> Option<u32> {
        let zero = |e: &Expr| matches!(&e.kind, ExprKind::Int(text) if super::scan::literal(text) == Some(0));
        if zero(b) && fa.1 == 0 && fa.0 != ZERO {
            Some(fa.0)
        } else if zero(a) && fb.1 == 0 && fb.0 != ZERO {
            Some(fb.0)
        } else {
            None
        }
    }

    /// `xs.is_empty()`, which is `xs.len() == 0`, and `m.contains(k)`, which makes `k` present
    /// where it is true (facts.conditions and facts.map-keys).
    fn called(
        &mut self,
        st: &State,
        owner: &stilt_hir::hir::Item,
        name: &str,
        args: &[crate::tast::Arg],
    ) -> (State, State) {
        let (mut t, mut f) = (st.clone(), st.clone());
        match (args, name) {
            ([xs], "is_empty") if is_prelude(owner, "List") => {
                if let ExprKind::Local(v) = xs.value.kind
                    && self.info.kind(v) == Kind::List
                    && let Some(&len) = st.lens.get(&v)
                {
                    t.facts.assume(len, ZERO, 0);
                    t.facts.assume(ZERO, len, 0);
                    f.facts.mark_nonzero(len);
                }
            }
            ([m, k], "contains") if is_prelude(owner, "Map") => {
                if let Some((_, version)) = self.map_of(st, &m.value)
                    && let Some(key) = self.key_of(st, &k.value)
                {
                    t.facts.present.insert((version, key));
                }
            }
            _ => {}
        }
        (t, f)
    }
}
