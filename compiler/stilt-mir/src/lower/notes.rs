//! What a comparison says when it fails in a test: the two sides, as `show_nested` shows them
//! (std.show-output). A failed `assert` panics with them in its detail, which program.panic-detail
//! leaves to each implementation for every kind but `explicit`, and a doc example that gives
//! `false` tells them to `stilt test` before it returns.

use stilt_hir::decls::prelude_item;
use stilt_hir::hir::BinaryOp;
use stilt_types::tast::{Expr, ExprKind};

use super::Lower;
use crate::mir::{Const, Operand, Runtime, Stmt};

/// A comparison of two values of a type that implements `Show`.
pub(crate) struct Compared<'e> {
    op: BinaryOp,
    left: &'e Expr,
    right: &'e Expr,
}

/// The operator as it is written.
fn spelled(op: BinaryOp) -> &'static str {
    match op {
        BinaryOp::Eq => "==",
        BinaryOp::Ne => "!=",
        BinaryOp::Lt => "<",
        BinaryOp::Le => "<=",
        BinaryOp::Gt => ">",
        _ => ">=",
    }
}

impl Lower<'_> {
    /// `e`, if it compares two values that `Show` shows.
    pub(crate) fn compared<'e>(&self, e: &'e Expr) -> Option<Compared<'e>> {
        let ExprKind::Binary(
            op @ (BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Le
            | BinaryOp::Gt
            | BinaryOp::Ge),
            left,
            right,
        ) = &e.kind
        else {
            return None;
        };
        self.implements(&left.ty, &prelude_item("Show"))
            .then_some(Compared {
                op: *op,
                left,
                right,
            })
    }

    /// The comparison `c`, whose sides are evaluated in order. Returns its result, and the
    /// words of the sides, to show them if it fails.
    pub(crate) fn compare(
        &mut self,
        c: &Compared<'_>,
        at: Operand,
    ) -> (Operand, Vec<Operand>, Vec<Operand>) {
        let left = self.expr(c.left);
        let right = self.expr(c.right);
        let result = self.binary_values(c.op, &c.left.ty, left.clone(), right.clone(), at);
        (result, left, right)
    }

    /// The text of the two sides of `c`, as `show_nested` shows them.
    pub(crate) fn shown_sides(
        &mut self,
        c: &Compared<'_>,
        (left, right): (Vec<Operand>, Vec<Operand>),
        at: &Operand,
    ) -> (Operand, Operand) {
        let shown = |l: &mut Self, e: &Expr, v| {
            l.trait_call("Show", "show_nested", &e.ty, vec![v], at.clone())
        };
        (shown(self, c.left, left), shown(self, c.right, right))
    }

    /// The value of a doc example that is a comparison: when it is `false`, the sides are told
    /// to `stilt test` first.
    pub(crate) fn noted_comparison(&mut self, c: &Compared<'_>, e: &Expr) -> Vec<Operand> {
        let at = self.loc_at(e.at);
        let (result, left, right) = self.compare(c, at.clone());
        let (failed, done) = (self.b.new_block(), self.b.new_block());
        self.b.branch(result.clone(), done, failed);
        self.b.switch_to(failed);
        let (a, b) = self.shown_sides(c, (left, right), &at);
        self.b.emit(Stmt::Effect(Runtime::TestNote, vec![a, b]));
        self.b.goto(done);
        self.b.switch_to(done);
        vec![result]
    }

    /// `assert c`, which panics with the sides in its detail when `c` is false.
    pub(crate) fn assert_compared(&mut self, c: &Compared<'_>, at: Operand) {
        let (result, left, right) = self.compare(c, at.clone());
        let (ok, failed) = (self.b.new_block(), self.b.new_block());
        self.b.branch(result, ok, failed);
        self.b.switch_to(failed);
        let (a, b) = self.shown_sides(c, (left, right), &at);
        let text = |s: &str| Operand::Const(Const::Str(s.into()));
        let operator = format!(" {} ", spelled(c.op));
        let detail = self.concat(vec![
            text("the assertion is false: "),
            a,
            text(&operator),
            b,
        ]);
        self.panic(6, Some(detail), at);
        self.b.switch_to(ok);
    }
}
