//! `when` (shared.when).

use stilt_diag::codes;
use stilt_hir::hir::{self, ExprKind, StmtKind};
use stilt_syntax::TextRange;

use super::{Cx, State, node};
use crate::tast;
use crate::ty::Ty;

/// The position of a block's value: its last expression's, or the `when`'s.
fn value_at(at: TextRange, b: &[hir::Stmt]) -> TextRange {
    match b.last() {
        Some(hir::Stmt {
            kind: StmtKind::Expr(e),
            ..
        }) => e.at,
        _ => at,
    }
}

impl State<'_> {
    /// `check` with no `wrap`, as in a closure or a `when`, where a `when` added around the
    /// statement would hold nothing the read can reach, or nest in another.
    pub(super) fn unwrapped<T>(&mut self, check: impl FnOnce(&mut Self) -> T) -> T {
        let outer = self.wrap.take();
        let checked = check(self);
        self.wrap = outer;
        checked
    }

    /// Each name stands, in the block, for the place of its handle's value, of type `T` for a
    /// handle of type `Shared<T>`, and E0433 for a handle of another type. A name that
    /// resolution reported holds a value of the error type. The `when`'s value is the block's.
    pub(super) fn when_expr(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        at: TextRange,
        held: &[hir::Held],
        block: &[hir::Stmt],
    ) -> tast::Expr {
        let held = held.iter().map(|h| self.held(cx, h)).collect();
        let (b, ty) = self.block_expr(cx, value_at(at, block), expected, block);
        node(tast::ExprKind::When(held, b), ty, at)
    }

    fn held(&mut self, cx: &mut Cx, h: &hir::Held) -> (tast::Expr, hir::LocalId) {
        let handle = self.infer(cx, None, &h.handle);
        let ty = match (&h.handle.kind, self.known(h.handle.at, &handle.ty)) {
            (ExprKind::Local(_), Some(t)) if t.shared().is_some() => {
                t.shared().cloned().unwrap_or(Ty::Error)
            }
            (ExprKind::Local(_), Some(t)) => {
                let name = &self.local_names[h.place.0 as usize];
                let message = format!(
                    "`{name}` has type `{}`, so `when` can't hold it; only a `Shared<T>` can be \
                     held",
                    self.show(&t)
                );
                self.error(codes::E0433, h.handle.at, message);
                Ty::Error
            }
            _ => {
                self.broken = true;
                Ty::Error
            }
        };
        self.locals.insert(h.place, ty);
        (handle, h.place)
    }
}
