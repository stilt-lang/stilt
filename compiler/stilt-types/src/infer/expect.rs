//! Expected types: requiring a type to be the one expected, and checking an expression against
//! one.

use stilt_diag::{Diagnostic, codes};
use stilt_hir::hir;
use stilt_syntax::TextRange;

use super::{Cx, State};
use crate::tast;
use crate::ty::{Kind, Ty};

impl State<'_> {
    fn mismatch(&mut self, at: TextRange, expected: &Ty, actual: &Ty) -> bool {
        let expected_ty = expected;
        let hint = if self.show(actual) == self.show(&Ty::option(expected.clone())) {
            "; it is `None` when a value is missing, so give a fallback with `else`"
        } else {
            ""
        };
        // A rigid type of a polymorphic function type on one side only is one that no type
        // argument makes the other side's (polymorphism.rigid-types).
        let (mut one, mut other) = (Vec::new(), Vec::new());
        super::poly::rigid_params(&self.table.freeze(expected), &mut one);
        super::poly::rigid_params(&self.table.freeze(actual), &mut other);
        let mut rigid: Vec<_> = one.iter().filter(|p| !other.contains(p)).cloned().collect();
        rigid.extend(other.iter().filter(|p| !one.contains(p)).cloned());
        let rigid = if rigid.is_empty() {
            String::new()
        } else {
            format!(
                ": no type argument of {} makes them equal",
                self.listed(&rigid)
            )
        };
        let help = self.null_help(expected, actual);
        let chain = self.chain(at, expected, actual);
        let (expected, actual) = self.table.show_diff(expected, actual, self.env.names);
        let message = format!("expected `{expected}`, found `{actual}`{hint}{rigid}");
        let d = Diagnostic::new(codes::E0311, at, message).with_chain(chain);
        self.errors.push(match help {
            Some(help) => d.with_help(help),
            None => d,
        });
        self.mismatches
            .push((self.errors.len() - 1, expected_ty.clone()));
        false
    }

    /// The chain of a mismatch at `at` (goal one-form-per-reader): where each side's variables
    /// were given their types, in the order they were, and last the mismatch itself.
    fn chain(&mut self, at: TextRange, expected: &Ty, actual: &Ty) -> Vec<(TextRange, String)> {
        let mut steps: Vec<(TextRange, String)> = Vec::new();
        let sides = [(expected, "expected"), (actual, "found")];
        for (side, word) in sides {
            for (solved, ty) in self.table.provenance(side) {
                let shown = self.show(&ty);
                if steps.iter().all(|(r, _)| *r != solved) && solved != at {
                    steps.push((solved, format!("this gives the {word} type `{shown}`")));
                }
            }
        }
        if let Some(v) = self.uses.get(&at).copied()
            && let Some(bound) = self.bound.get(&v).copied()
            && steps.iter().all(|(r, _)| *r != bound)
        {
            let name = &self.local_names[v.0 as usize];
            let shown = self.show(actual);
            steps.push((
                bound,
                format!("`{name}` is bound here, with the type `{shown}`"),
            ));
        }
        steps.sort_by_key(|(r, _)| r.start());
        let (shown_expected, shown_actual) = (self.show(expected), self.show(actual));
        steps.push((
            at,
            format!("here `{shown_actual}` is found where `{shown_expected}` is expected"),
        ));
        steps
    }

    /// The help of a mismatch where an `Option` of a type not yet known, as `None` is, stands
    /// where a value of a type that isn't an `Option` is expected, as another language's null
    /// would.
    fn null_help(&mut self, expected: &Ty, actual: &Ty) -> Option<String> {
        let (expected, actual) = (self.resolved(expected), self.resolved(actual));
        let Ty::Con(_, args) = &actual else {
            return None;
        };
        let unknown = matches!(args.first().map(|a| self.resolved(a)), Some(Ty::Var(_)));
        if !actual.is_prelude("Option") || expected.is_prelude("Option") || !unknown {
            return None;
        }
        let shown = self.show(&expected);
        Some(format!(
            "Stilt has no null: a value that may be missing has the type `Option<{shown}>`, \
             which is `None` or `Some(x)`. Write that type where the value is expected, or give \
             a value of type `{shown}`."
        ))
    }

    /// Requires `actual` to be `expected`, and tells whether it is.
    pub(super) fn agrees(&mut self, at: TextRange, expected: &Ty, actual: &Ty) -> bool {
        let agrees =
            self.table.at(at, |t| t.unify(actual, expected)) || self.mismatch(at, expected, actual);
        self.escaped_here(at);
        agrees
    }

    /// meta.leaving-arm: E0351 where the expression at `at` made a type left open outside an arm
    /// hold one of the arm's fresh types.
    fn escaped_here(&mut self, at: TextRange) {
        if self.regions_open() > 0 {
            self.escaped(at);
        }
    }

    pub(super) fn expect(&mut self, at: TextRange, expected: &Ty, actual: &Ty) {
        self.agrees(at, expected, actual);
    }

    /// Requires a value of type `actual` to be usable where `expected` is, and tells whether it
    /// is: a value of type `Never` fits anywhere, and a function fits where a function type
    /// with a larger row is expected (declarations.never; effects.function-values).
    pub(super) fn fits(&mut self, at: TextRange, expected: &Ty, actual: &Ty) -> bool {
        let fits = self.fits_quietly(expected, actual) || self.mismatch(at, expected, actual);
        self.escaped_here(at);
        fits
    }

    /// Whether a value of type `actual` is usable where `expected` is, as [`State::fits`]
    /// says, without reporting it.
    pub(super) fn fits_quietly(&mut self, expected: &Ty, actual: &Ty) -> bool {
        match (self.resolved(actual), self.resolved(expected)) {
            (a, _) if a == Ty::never() => true,
            (Ty::Fn(f), Ty::Fn(g))
                if f.params.len() == g.params.len() && !f.is_poly() && !g.is_poly() =>
            {
                f.params
                    .iter()
                    .zip(&g.params)
                    .all(|((m, x), (n, y))| m == n && self.table.unify(y, x))
                    && self.table.unify(&f.ret, &g.ret)
                    && self
                        .table
                        .fit(&crate::ty::Handled::Nothing, &f.row, &g.row)
                        .is_empty()
            }
            _ => self.table.unify(actual, expected),
        }
    }

    pub(super) fn subsume(&mut self, at: TextRange, expected: &Ty, actual: &Ty) {
        self.fits(at, expected, actual);
    }

    /// A type that values of type `t` fit in, whose function row may grow to hold the rows of
    /// other function values (effects.function-value-unions).
    pub(super) fn widen(&mut self, t: &Ty) -> Ty {
        match self.resolved(t) {
            Ty::Fn(f) => {
                let row = self.table.fresh_row(true);
                Ty::func(f.params, f.ret, row)
            }
            t => t,
        }
    }

    /// A type that must be known where it is used, as a receiver's is (traits.method-resolution). A
    /// literal's type takes its default there (numbers.literal-defaults).
    pub(super) fn known(&mut self, at: TextRange, t: &Ty) -> Option<Ty> {
        self.settle_args();
        match self.table.unsolved(t).map(|v| v.kind) {
            Some(Kind::IntLiteral) => self.table.solve(t, Ty::i64()),
            Some(Kind::FloatLiteral) => self.table.solve(t, Ty::f64()),
            _ => {}
        }
        match self.resolved(t) {
            Ty::Error => None,
            Ty::Var(_) => {
                if let Some(v) = self.table.unsolved(t)
                    && !v.tainted
                    && !self.unknown.contains(&v.id)
                {
                    self.unknown.push(v.id);
                    let message =
                        "the type of this expression must be known here; add an annotation";
                    self.error(codes::E0312, at, message.to_owned());
                }
                None
            }
            t => Some(t),
        }
    }

    /// Checks `e` against `expected`, telling whether it fits.
    pub(super) fn check_fits(
        &mut self,
        cx: &mut Cx,
        expected: &Ty,
        e: &hir::Expr,
    ) -> (tast::Expr, bool) {
        if let Ty::Fn(p) = self.table.resolve(expected)
            && p.is_poly()
        {
            let p = p.clone();
            return self.check_poly(cx, &p, e);
        }
        let v = self.infer(cx, Some(expected), e);
        if matches!(self.table.resolve(expected), Ty::Error) {
            self.unchecked_literal(&v);
        }
        let fits = self.fits(e.at, expected, &v.ty);
        if !fits {
            self.offer_conversion(e.at, e, (&v.ty, expected));
        }
        (v, fits)
    }

    /// A literal whose expected type is the error type, a failed use's among them, has that
    /// type, and its range isn't checked (macros.failed-uses; errors.error-type).
    fn unchecked_literal(&mut self, v: &tast::Expr) {
        let literal =
            |e: &tast::Expr| matches!(e.kind, tast::ExprKind::Int(_) | tast::ExprKind::Float(_));
        let is_literal = match &v.kind {
            tast::ExprKind::Unary(hir::UnaryOp::Neg, x) => literal(x) && x.ty == v.ty,
            _ => literal(v),
        };
        if is_literal && self.table.unsolved(&v.ty).is_some() {
            self.literals.retain(|l| l.ty != v.ty);
            self.table.solve(&v.ty, Ty::Error);
        }
    }

    pub(super) fn check(&mut self, cx: &mut Cx, expected: &Ty, e: &hir::Expr) -> tast::Expr {
        self.check_fits(cx, expected, e).0
    }

    /// Checks an expression whose expected type an error hides, as the error type, so that it
    /// causes no error of its own (errors.error-type).
    pub(super) fn abandon(&mut self, cx: &mut Cx, e: &hir::Expr) -> tast::Expr {
        self.check(cx, &Ty::Error, e)
    }

    /// Checks `e` against `expected` when there is one.
    pub(super) fn infer_checked(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        e: &hir::Expr,
    ) -> tast::Expr {
        match expected {
            Some(t) => self.check(cx, t, e),
            None => self.infer(cx, None, e),
        }
    }

    /// The type that the first branch of an `if`, a `match` or a `try … catch` whose type isn't
    /// expected gives the later branches, which are checked against it (expressions.if). A function
    /// type's row grows to hold theirs (effects.function-values). `None` while every branch so far
    /// has type `Never`.
    pub(super) fn settled(&mut self, ty: &Ty, at: TextRange) -> Option<Ty> {
        if self.is_never(ty) {
            return None;
        }
        let common = self.widen(ty);
        self.subsume(at, &common, ty);
        Some(common)
    }
}
