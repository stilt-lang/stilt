//! `with` (handlers.with).

use stilt_diag::codes;
use stilt_hir::hir::{self, StmtKind};
use stilt_syntax::TextRange;

use super::effects::Reported;
use super::{Cx, State, error_node, node};
use crate::tast;
use crate::ty::{Handled, HandlerTy, Ty};

/// The position of a block's value, where E0311 reports one that isn't the `R` of a handler
/// that takes control.
fn value_at(at: TextRange, b: &[hir::Stmt]) -> TextRange {
    match b.last() {
        Some(hir::Stmt {
            kind: StmtKind::Expr(e),
            ..
        }) => e.at,
        _ => at,
    }
}

/// A context for code inside `cx`'s, whose effects are its own.
fn within(cx: &Cx) -> Cx {
    let mut inner = Cx::new(cx.ret.clone());
    inner.yields.clone_from(&cx.yields);
    inner.known.clone_from(&cx.known);
    inner.resume.clone_from(&cx.resume);
    inner
}

/// What a `with` runs installed: its block, or, for `with a, b { … }`, the `with b { … }` in it.
struct Inside<'h> {
    rest: &'h [hir::Expr],
    block: &'h [hir::Stmt],
    at: TextRange,
}

impl State<'_> {
    /// handlers.with: `with a, b { … }` is `with a { with b { … } }`.
    pub(super) fn with_expr(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        at: TextRange,
        handlers: &[hir::Expr],
        block: &[hir::Stmt],
    ) -> tast::Expr {
        let Some((h, rest)) = handlers.split_first() else {
            unreachable!("a `with` names a handler")
        };
        let hv = self.infer(cx, None, h);
        let inside = Inside { rest, block, at };
        match self.known(h.at, &hv.ty) {
            Some(Ty::Handler(hty)) => self.installed(cx, expected, hv, &hty, &inside),
            Some(t) => {
                let message = format!("expected a handler, found `{}`", self.show(&t));
                self.error(codes::E0311, h.at, message);
                self.broken_with(cx, expected, &inside)
            }
            None => self.broken_with(cx, expected, &inside),
        }
    }

    /// The block, or the nested `with`, checked in `inner`.
    fn inside(
        &mut self,
        inner: &mut Cx,
        expected: Option<&Ty>,
        i: &Inside<'_>,
    ) -> (tast::Block, Ty) {
        if i.rest.is_empty() {
            return self.block_expr(inner, value_at(i.at, i.block), expected, i.block);
        }
        let w = self.with_expr(inner, expected, i.at, i.rest, i.block);
        let ty = w.ty.clone();
        let stmt = tast::Stmt {
            kind: tast::StmtKind::Expr(w),
            at: i.at,
        };
        (vec![stmt], ty)
    }

    /// A `with` whose handler has an error, or isn't a handler: its block is checked, and the
    /// `with` has the error type.
    fn broken_with(&mut self, cx: &Cx, expected: Option<&Ty>, i: &Inside<'_>) -> tast::Expr {
        let mut inner = within(cx);
        self.inside(&mut inner, expected, i);
        self.broken = true;
        error_node(i.at)
    }

    /// handlers.with: the block, run with the handler `hv` of type `hty` installed. Its effects
    /// reach the `with` without the handled effect, whose arguments must be the handler's, and the
    /// `with` performs them, the handler type's row and its operations' effects. With `-> R`, the
    /// block, and so the `with`, has type `R` (handlers.resuming).
    fn installed(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        hv: tast::Expr,
        hty: &HandlerTy,
        i: &Inside<'_>,
    ) -> tast::Expr {
        let mut inner = within(cx);
        inner
            .known
            .insert(0, (hty.effect.clone(), hty.args.clone()));
        let (b, ty) = match &hty.answer {
            None => self.inside(&mut inner, expected, i),
            Some(r) => {
                let (b, t) = self.inside(&mut inner, None, i);
                let at = if i.rest.is_empty() {
                    value_at(i.at, i.block)
                } else {
                    i.at
                };
                let ty = if self.fits(at, r, &t) {
                    r.clone()
                } else {
                    Ty::Error
                };
                (b, ty)
            }
        };
        let passed = self.table.fresh_row(false);
        let handled = Handled::Effect(hty.effect.clone(), hty.args.clone());
        let mut reported = Reported::default();
        for (row, row_at) in &inner.effects {
            let problems = self.table.fit(&handled, row, &passed);
            self.report(&mut reported, (*row_at, false), problems);
        }
        cx.perform(passed, i.at);
        cx.perform(hty.row.clone(), i.at);
        cx.perform(self.operation_effects(hty), i.at);
        let with = tast::ExprKind::With(Box::new(hv), hty.effect.clone(), hty.args.clone(), b);
        node(with, ty, i.at)
    }
}
