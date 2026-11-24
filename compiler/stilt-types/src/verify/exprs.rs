//! The value of each expression (facts.linear-forms and facts.intervals), evaluated in the order of
//! values.left-to-right and values.assignment-order, and the overflows and divisions it proves
//! (facts.proved-divisions and facts.proved-overflow).

use stilt_hir::hir::{BinaryOp, Item, LocalId, Name, UnaryOp};

use super::Check;
use super::dbm::ZERO;
use super::scan::{Kind, literal};
use super::state::State;
use super::values::{self, Value, cut, type_bounds, within};
use super::walker::Walker;
use crate::tast::{Expr, ExprKind, Segment};
use crate::ty::Ty;

/// The bounds of an integer type.
pub(crate) fn bounds_of(ty: &Ty) -> Option<(i128, i128)> {
    ty.integer_name().and_then(type_bounds)
}

/// How many terms the facts of one statement hold before an expression's end drops the dead ones.
const EXPRESSION_TERMS: usize = 256;

impl Walker<'_> {
    /// Evaluates an expression, and gives its value if it is an integer.
    pub(crate) fn eval(&mut self, st: &mut State, e: &Expr) -> Option<Value> {
        let value = self.eval_kind(st, e);
        if e.ty == Ty::never() {
            // A call of type `Never`, or any other expression of it, leaves
            // (facts.paths-that-leave).
            st.facts.unreached();
        }
        // Each operator of a long chain, such as `-` 100,000 times, makes a term, and the terms
        // its operands made are dead once it has its value. They are dropped as at a statement's
        // end, which keeps every fact between the others, once the facts have doubled since the
        // last drop, so that the drops cost no more than the terms did.
        if st.facts.terms().len() > (2 * self.kept).max(EXPRESSION_TERMS) {
            self.end_stmt(st, value);
        }
        value
    }

    fn eval_kind(&mut self, st: &mut State, e: &Expr) -> Option<Value> {
        match &e.kind {
            ExprKind::Int(text) => self.literal(st, e, literal(text)),
            ExprKind::Unary(UnaryOp::Neg, x) if matches!(x.kind, ExprKind::Int(_)) => {
                let ExprKind::Int(text) = &x.kind else {
                    return None;
                };
                self.literal(st, e, literal(text).map(|n| -n))
            }
            ExprKind::Local(v) => self.local(st, *v, &e.ty),
            ExprKind::Constant(item) => self.constant(st, item, None, &e.ty),
            ExprKind::MemberConstant(item, name, _) => self.constant(st, item, Some(*name), &e.ty),
            ExprKind::ValueParam(id) => match self.values.get(id) {
                Some(&t) => Some(Walker::linear(st, t, 0)),
                None => self.opaque(st, &e.ty),
            },
            ExprKind::Field(b, _) | ExprKind::TupleField(b, _) => {
                self.eval(st, b);
                self.opaque(st, &e.ty)
            }
            ExprKind::Index(c, k) => self.index(st, c, k, e),
            ExprKind::Unary(op, x) => self.unary(st, *op, x, e),
            ExprKind::Binary(op, a, b) => self.binary(st, *op, a, b, e),
            ExprKind::Call(..) | ExprKind::Project(..) => self.call(st, e),
            ExprKind::CallValue(f, args) => {
                self.eval(st, f);
                self.call_value(st, &f.ty, args, e)
            }
            ExprKind::Block(b) => self.block(st, b),
            ExprKind::Closure(..) | ExprKind::Handler(_) => {
                self.closures(e);
                None
            }
            ExprKind::Return(x) => {
                if let Some(x) = x {
                    self.eval(st, x);
                }
                st.facts.unreached();
                None
            }
            ExprKind::Raise(x) => {
                self.eval(st, x);
                self.leaves(st, Some(&x.ty), false);
                st.facts.unreached();
                None
            }
            ExprKind::Break => {
                self.jump(st, false);
                None
            }
            ExprKind::Continue => {
                self.jump(st, true);
                None
            }
            _ => self.control(st, e),
        }
    }

    /// A closure, or a handler's operations, each analysed as a body of its own
    /// (facts.verification).
    fn closures(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Closure(params, body) => self.closure(params, body),
            ExprKind::Handler(h) => {
                for (_, op) in &h.ops {
                    if let ExprKind::Closure(params, body) = &op.kind {
                        self.closure(params, body);
                    }
                }
            }
            _ => {}
        }
    }

    /// The forms that hold blocks, and those whose parts are evaluated in order and give no
    /// integer of a linear form.
    fn control(&mut self, st: &mut State, e: &Expr) -> Option<Value> {
        match &e.kind {
            ExprKind::If(c, then, otherwise) => {
                self.if_else(st, c, then, otherwise.as_deref(), &e.ty)
            }
            ExprKind::IfLet(p, scrutinee, then, otherwise) => {
                self.if_let(st, (p, scrutinee), then, otherwise.as_deref(), &e.ty)
            }
            ExprKind::Match(scrutinee, arms) => self.matches(st, scrutinee, arms, &e.ty),
            ExprKind::Else(a, b) => self.else_(st, a, b, &e.ty),
            ExprKind::Try(x, catch) => self.try_(st, x, catch.as_ref(), &e.ty),
            ExprKind::Loop(b) => self.loop_(st, b, e),
            ExprKind::While(c, b) => self.while_(st, c, b),
            ExprKind::For(p, iterable, b) => self.for_(st, p, iterable, b, e),
            ExprKind::With(h, _, _, b) => self.with(st, h, b, &e.ty),
            ExprKind::When(held, b) => {
                for (h, _) in held {
                    self.eval(st, h);
                }
                self.block(st, b);
                self.opaque(st, &e.ty)
            }
            ExprKind::Spread(s) => {
                self.spread(st, &s.body, e);
                self.opaque(st, &e.ty)
            }
            ExprKind::Interpolated(segments) => {
                for s in segments {
                    if let Segment::Splice(x, _) = s {
                        self.eval(st, x);
                    }
                }
                None
            }
            _ => {
                for c in crate::tast::walk::children(e) {
                    self.eval(st, c);
                }
                self.opaque(st, &e.ty)
            }
        }
    }

    /// A literal's value: zero plus its number.
    fn literal(&mut self, st: &mut State, e: &Expr, n: Option<i128>) -> Option<Value> {
        bounds_of(&e.ty)?;
        match n {
            Some(n) => Some(Value {
                term: ZERO,
                d: n,
                linear: true,
                lo: Some(n),
                hi: Some(n),
            }),
            None => self.opaque(st, &e.ty),
        }
    }

    /// A value with no linear form and no facts but its type's bounds, when it is an integer.
    pub(crate) fn opaque(&mut self, st: &mut State, ty: &Ty) -> Option<Value> {
        let b = bounds_of(ty)?;
        Some(self.made(st, b))
    }

    /// A binding's value: its current term plus 0, for an integer binding (facts.linear-forms). A
    /// name of a `when` has no term (facts.terms).
    fn local(&mut self, st: &mut State, v: LocalId, ty: &Ty) -> Option<Value> {
        match (self.info.kind(v), st.ints.get(&v)) {
            (Kind::Int(..), Some(&t)) => Some(Walker::linear(st, t, 0)),
            (Kind::Int(..), None) => {
                self.declare(st, v);
                let t = *st.ints.get(&v)?;
                Some(Walker::linear(st, t, 0))
            }
            _ => self.opaque(st, ty),
        }
    }

    /// A constant written as an integer literal stands for its number; any other has no term of
    /// its own (facts.terms).
    fn constant(
        &mut self,
        st: &mut State,
        item: &Item,
        member: Option<Name>,
        ty: &Ty,
    ) -> Option<Value> {
        bounds_of(ty)?;
        match (self.cx.literal)(item, member) {
            Some(n) => Some(Value {
                term: ZERO,
                d: n,
                linear: true,
                lo: Some(n),
                hi: Some(n),
            }),
            None => self.opaque(st, ty),
        }
    }

    /// The literal or facts.terms constant that an expression is, if it is one.
    pub(crate) fn number(&self, e: &Expr) -> Option<i128> {
        match &e.kind {
            ExprKind::Int(text) => literal(text),
            ExprKind::Unary(UnaryOp::Neg, x) => match &x.kind {
                ExprKind::Int(text) => literal(text).map(|n| -n),
                _ => None,
            },
            ExprKind::Constant(item) => (self.cx.literal)(item, None),
            ExprKind::MemberConstant(item, name, _) => (self.cx.literal)(item, Some(*name)),
            _ => None,
        }
    }

    fn unary(&mut self, st: &mut State, op: UnaryOp, x: &Expr, e: &Expr) -> Option<Value> {
        let a = self.eval(st, x);
        let ty = bounds_of(&e.ty)?;
        let a = a?;
        if op != UnaryOp::Neg {
            return Some(self.made(st, ty));
        }
        let exact = values::neg(a.interval());
        self.overflow(e, exact, ty);
        Some(self.made(st, cut(exact, ty)))
    }

    /// Records whether an arithmetic operation, whose exact result lies in `exact`, overflows
    /// (facts.proved-overflow).
    pub(crate) fn overflow(&mut self, e: &Expr, exact: values::Interval, ty: (i128, i128)) {
        self.prove(e.at, Check::Overflow, within(exact, ty));
    }

    fn binary(
        &mut self,
        st: &mut State,
        op: BinaryOp,
        left: &Expr,
        right: &Expr,
        expr: &Expr,
    ) -> Option<Value> {
        match op {
            BinaryOp::And | BinaryOp::Or => {
                let (t, f) = self.cond(st, expr);
                *st = self.join(vec![t, f]);
                return None;
            }
            _ => {}
        }
        let lhs = self.eval(st, left);
        let held: Vec<_> = lhs.iter().map(|v| v.term).collect();
        let rhs = self.holding(&held, |w| w.eval(st, right));
        let ty = bounds_of(&expr.ty)?;
        let (lhs, rhs) = (lhs?, rhs?);
        Some(self.arithmetic(st, op, (left, lhs), (right, rhs), expr, ty))
    }

    /// `a op b` on integers, `a` and `b` evaluated to `x` and `y`: a linear form when `b` is a
    /// literal or a facts.terms constant, as `e + c` (facts.linear-forms), and otherwise a new term
    /// with its interval and relative bounds, and the checks it proves.
    pub(crate) fn arithmetic(
        &mut self,
        st: &mut State,
        op: BinaryOp,
        (left, lhs): (&Expr, Value),
        (right, rhs): (&Expr, Value),
        expr: &Expr,
        ty: (i128, i128),
    ) -> Value {
        if let Some(value) = self.offset(st, op, (left, lhs), (right, rhs), expr, ty) {
            return value;
        }
        match op {
            BinaryOp::Add => {
                let value = self.sum(st, op, lhs, rhs, expr, ty);
                self.midpoint(st, left, right, value.term);
                value
            }
            BinaryOp::Sub | BinaryOp::Mul => self.sum(st, op, lhs, rhs, expr, ty),
            BinaryOp::Div | BinaryOp::Rem => {
                self.division(st, op, (left, lhs), (right, rhs), expr, ty)
            }
            BinaryOp::Shl | BinaryOp::Shr => {
                let width = expr.ty.integer_name().and_then(values::width).unwrap_or(64);
                let ok = within(rhs.interval(), (0, width - 1));
                self.prove(expr.at, Check::Overflow, ok);
                self.made(st, ty)
            }
            _ => self.made(st, ty),
        }
    }

    /// `e + c`, `c + e` and `e - c`, for `e` of a linear form and `c` a literal or a facts.terms
    /// constant: a linear form, whose interval is the exact result's (facts.linear-forms and
    /// facts.proved-overflow).
    fn offset(
        &mut self,
        st: &State,
        op: BinaryOp,
        (left, lhs): (&Expr, Value),
        (right, rhs): (&Expr, Value),
        expr: &Expr,
        ty: (i128, i128),
    ) -> Option<Value> {
        let (form, offset) = match op {
            BinaryOp::Add => match (
                lhs.form(),
                self.number(right),
                rhs.form(),
                self.number(left),
            ) {
                (Some(form), Some(offset), ..) | (_, _, Some(form), Some(offset)) => (form, offset),
                _ => return None,
            },
            BinaryOp::Sub => (lhs.form()?, -self.number(right)?),
            _ => return None,
        };
        let value = Walker::linear(st, form.0, form.1 + offset);
        self.overflow(expr, value.interval(), ty);
        Some(value)
    }

    /// `a + b`, `a - b` and `a * b` with no linear form: the exact interval cut to the type's
    /// bounds, and for `+` and `-` the relative bounds of facts.intervals and
    /// facts.relative-bounds.
    fn sum(
        &mut self,
        st: &mut State,
        op: BinaryOp,
        lhs: Value,
        rhs: Value,
        expr: &Expr,
        ty: (i128, i128),
    ) -> Value {
        let exact = match op {
            BinaryOp::Add => values::add(lhs.interval(), rhs.interval()),
            BinaryOp::Sub => values::sub(lhs.interval(), rhs.interval()),
            _ => values::mul(lhs.interval(), rhs.interval()),
        };
        self.overflow(expr, exact, ty);
        let value = self.made(st, cut(exact, ty));
        let relative = |st: &mut State, form: (u32, i128), (low, high): values::Interval| {
            if let Some(low) = low {
                st.facts.assume(form.0, value.term, -(form.1 + low));
            }
            if let Some(high) = high {
                st.facts.assume(value.term, form.0, form.1 + high);
            }
        };
        match op {
            BinaryOp::Add => {
                if let Some(form) = lhs.form() {
                    relative(st, form, rhs.interval());
                }
                if let Some(form) = rhs.form() {
                    relative(st, form, lhs.interval());
                }
            }
            BinaryOp::Sub => {
                if let Some(form) = lhs.form() {
                    relative(st, form, values::neg(rhs.interval()));
                }
            }
            _ => {}
        }
        value
    }
}
