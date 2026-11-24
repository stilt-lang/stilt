//! The operations that can overflow (numbers.integer-panics and numbers.shifts;
//! effects.overflow-effect): integer `+`, `-` and `*`, their compound assignments, `-` on a value
//! that isn't a literal, `/` and `%` on a signed type unless the divisor is a literal other than
//! `-1`, and a shift unless its amount is a literal below the left operand's width. Wrapping
//! operators can't. A call of `div_euclid` or `rem_euclid` by a literal names no native
//! (std.integers), so its overflow by `-1` is its own.

use stilt_hir::hir::{BinaryOp, UnaryOp};
use stilt_syntax::TextRange;

use super::{Fact, Finder, Site};
use crate::literal::int_canonical;
use crate::tast::{Callee, Expr, ExprKind, Stmt, StmtKind};
use crate::ty::Ty;

/// The value of an integer literal, `-` before one included, when it fits in an `i64`. The
/// canonical text of zero is empty.
fn literal(e: &Expr) -> Option<i64> {
    let value = |text: &str| match int_canonical(text).as_str() {
        "" => Some(0),
        canonical => canonical.parse::<i64>().ok(),
    };
    match &e.kind {
        ExprKind::Int(text) => value(text),
        ExprKind::Unary(UnaryOp::Neg, operand) => match &operand.kind {
            ExprKind::Int(text) => value(text).map(|v| -v),
            _ => None,
        },
        _ => None,
    }
}

/// The width of an integer type, and whether it is signed.
fn integer(ty: &Ty) -> Option<(i64, bool)> {
    let name = ty.integer_name()?;
    Some((name[1..].parse().unwrap_or(64), name.starts_with('i')))
}

/// The operator as messages name it, if `op` on `left`'s type, with `right` its second operand,
/// can overflow.
fn binary(op: BinaryOp, left: &Ty, right: &Expr) -> Option<&'static str> {
    let (width, signed) = integer(left)?;
    match op {
        BinaryOp::Add => Some("`+`"),
        BinaryOp::Sub => Some("`-`"),
        BinaryOp::Mul => Some("`*`"),
        BinaryOp::Div | BinaryOp::Rem if signed && literal(right).is_none_or(|v| v == -1) => {
            Some(if op == BinaryOp::Div { "`/`" } else { "`%`" })
        }
        BinaryOp::Shl | BinaryOp::Shr
            if literal(right).is_none_or(|v| !(0..width).contains(&v)) =>
        {
            Some(if op == BinaryOp::Shl { "`<<`" } else { "`>>`" })
        }
        _ => None,
    }
}

impl Finder<'_> {
    /// Records an operation that can overflow, as `what` names it.
    fn overflows(&self, at: TextRange, what: &str) {
        self.push(Site {
            overflow: Some(Fact::noun(what)),
            ..Site::new(at, Vec::new())
        });
    }

    /// The overflow of a compound assignment, as `s += x`.
    pub(super) fn overflow_stmt(&self, s: &Stmt) {
        if let StmtKind::Assign(Some(op), p, v) = &s.kind
            && let Some(what) = binary(*op, &p.ty, v)
        {
            let what = format!("{}=`", what.trim_end_matches('`'));
            self.overflows(s.at, &what);
        }
    }

    /// The overflow of an operator, as `a + b` or `-a`.
    pub(super) fn overflow_expr(&self, e: &Expr) {
        match &e.kind {
            ExprKind::Binary(op, a, b) => {
                if let Some(what) = binary(*op, &a.ty, b) {
                    self.overflows(e.at, what);
                }
            }
            ExprKind::Unary(UnaryOp::Neg, a)
                if literal(e).is_none() && integer(&a.ty).is_some_and(|(_, signed)| signed) =>
            {
                self.overflows(e.at, "`-`");
            }
            ExprKind::Call(Callee::Member(_, name), _, args, _)
                if matches!(&**name, "div_euclid" | "rem_euclid")
                    && let [a, b] = args.as_slice()
                    && integer(&a.value.ty).is_some_and(|(_, signed)| signed)
                    && literal(&b.value) == Some(-1) =>
            {
                self.overflows(e.at, &format!("`{name}` by `-1`"));
            }
            _ => {}
        }
    }
}
