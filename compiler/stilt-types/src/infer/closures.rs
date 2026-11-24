//! Closures, and key paths, which stand for closures (expressions.key-paths).

use stilt_diag::codes;
use stilt_hir::hir::{self, ClosureParam, ExprKind, LocalId, Mode};
use stilt_syntax::TextRange;

use super::{Cx, State, error_node, node};
use crate::tast;
use crate::ty::{Row, Ty};

/// Whether an expression is a key path: `.` followed by fields, indexes and calls.
pub(super) fn key_path(e: &hir::Expr) -> bool {
    match &e.kind {
        ExprKind::KeyRoot => true,
        ExprKind::Field(base, _) | ExprKind::Index(base, _) => key_path(base),
        ExprKind::Call(callee, _) => key_path(callee),
        _ => false,
    }
}

/// The key path `e` with its root replaced by the variable `v`. The arguments and indexes in
/// the chain are expressions of their own, where a key path starts afresh.
fn rebase(e: &hir::Expr, v: LocalId) -> hir::Expr {
    let kind = match &e.kind {
        ExprKind::KeyRoot => ExprKind::Local(v),
        ExprKind::Field(base, field) => ExprKind::Field(Box::new(rebase(base, v)), field.clone()),
        ExprKind::Index(base, index) => ExprKind::Index(Box::new(rebase(base, v)), index.clone()),
        ExprKind::Call(callee, args) => ExprKind::Call(Box::new(rebase(callee, v)), args.clone()),
        _ => return e.clone(),
    };
    hir::Expr { kind, at: e.at }
}

/// A function type's parameters, return type and row.
type Parts = (Vec<(Mode, Ty)>, Ty, Row);

impl State<'_> {
    /// expressions.key-paths: `.chain` means `|x| x.chain` where a function type of one parameter
    /// is expected.
    pub(super) fn key_path_closure(&mut self, expected: Option<&Ty>, e: &hir::Expr) -> tast::Expr {
        let expected = expected.map(|t| self.resolved(t));
        match expected {
            Some(Ty::Fn(f)) if matches!(f.params.as_slice(), [(Mode::Let, _)]) => {
                let param = f.params[0].1.clone();
                let v = self.synthetic("it");
                self.locals.insert(v, param.clone());
                let mut inner = Cx::new(f.ret.clone());
                self.enter_regions(&mut inner);
                let body = self.check(&mut inner, &f.ret, &rebase(e, v));
                self.settle(&inner.effects, &f.row, false);
                let p = tast::Pat {
                    kind: tast::PatKind::Bind(v),
                    ty: param.clone(),
                    at: e.at,
                };
                let ty = Ty::func(vec![(Mode::Let, param)], f.ret, f.row);
                node(tast::ExprKind::Closure(vec![p], Box::new(body)), ty, e.at)
            }
            Some(Ty::Error) => error_node(e.at),
            _ => {
                let message = "a key path is allowed only where a function type is expected";
                self.error(codes::E0324, e.at, message.to_owned());
                error_node(e.at)
            }
        }
    }

    /// A closure's parameter, whose type is `expected` where the closure's type is expected.
    fn closure_param(&mut self, cx: &mut Cx, p: &ClosureParam, expected: Option<&Ty>) -> tast::Pat {
        let ty = match (&p.annotation, expected) {
            (Some(a), Some(t)) => {
                // A parameter whose annotation contradicts its expected type has the error
                // type.
                let a = self.of_hir(a);
                if self.agrees(p.pattern.at, t, &a) {
                    a
                } else {
                    Ty::Error
                }
            }
            (Some(a), None) => self.of_hir(a),
            (None, Some(t)) => t.clone(),
            (None, None) => self.fresh(p.pattern.at),
        };
        let checked = self.pattern(cx, &p.pattern, &ty);
        self.require_irrefutable(&p.pattern);
        checked
    }

    /// The type a closure of `n` parameters is expected to have: a spread among the expected
    /// parameters takes as many as the closure has (variadics.pack-inference).
    fn fitted(&mut self, t: &Ty, n: usize) -> Ty {
        match self.resolved(t) {
            Ty::Fn(mut f) if f.has_spread() => {
                f.params = self.table.fit_params(&f.params, n);
                Ty::Fn(f)
            }
            t => t,
        }
    }

    /// The context of a closure literal's body: it knows its row's effects
    /// (handlers.performing-operation), and a `resume` in it is its operation's, which E0514 rules
    /// out (handlers.resume-outside-operation).
    fn closure_cx(&self, cx: &Cx, ret: &Ty, row: &crate::ty::Row) -> Cx {
        let mut inner = Cx::new(ret.clone());
        self.enter_regions(&mut inner);
        inner.known = self.table.row_contents(row).effects;
        inner.resume.clone_from(&cx.resume);
        inner
    }

    pub(super) fn closure(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        at: TextRange,
        params: &[ClosureParam],
        body: &hir::Expr,
    ) -> tast::Expr {
        // A closure expected to have the error type, or the wrong number of parameters, has
        // the error type, and so do its parameters.
        let unknown = || {
            (
                params
                    .iter()
                    .map(|_| (Mode::Let, Ty::Error))
                    .collect::<Vec<_>>(),
                Ty::Error,
            )
        };
        let unknown_row = self.table.fresh_row(false);
        let expected = expected.map(|t| self.fitted(t, params.len()));
        let expected = expected.as_ref();
        let (arity_ok, expected_fn): (bool, Option<Parts>) =
            match expected.map(|t| self.resolved(t)) {
                Some(Ty::Fn(f)) if f.params.len() == params.len() => {
                    (true, Some((f.params, f.ret, f.row)))
                }
                Some(Ty::Fn(f)) => {
                    let (n, m) = (params.len(), f.params.len());
                    let message = format!(
                        "this closure takes {n} parameter{}, but {m} {} expected",
                        if n == 1 { "" } else { "s" },
                        if m == 1 { "is" } else { "are" }
                    );
                    self.error(codes::E0315, at, message);
                    let (ps, ret) = unknown();
                    (false, Some((ps, ret, unknown_row)))
                }
                Some(Ty::Error) => {
                    let (ps, ret) = unknown();
                    (true, Some((ps, ret, unknown_row)))
                }
                _ => (true, None),
            };
        let patterns: Vec<tast::Pat> = params
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let expected = expected_fn.as_ref().map(|(ps, _, _)| ps[i].1.clone());
                self.closure_param(cx, p, expected.as_ref())
            })
            .collect();
        let (ret, row) = match expected_fn {
            Some((_, ret, row)) => (ret, row),
            None => (self.fresh(body.at), self.table.fresh_row(true)),
        };
        let mut inner = self.closure_cx(cx, &ret, &row);
        let b = self.check(&mut inner, &ret, body);
        self.settle(&inner.effects, &row, false);
        let ty = if arity_ok {
            // An `inout` parameter makes an `inout` parameter of the closure's type
            // (expressions.inout-closure-parameters).
            let params = params
                .iter()
                .zip(&patterns)
                .map(|(param, p)| (param.mode, p.ty.clone()))
                .collect();
            Ty::func(params, ret, row)
        } else {
            Ty::Error
        };
        node(tast::ExprKind::Closure(patterns, Box::new(b)), ty, at)
    }
}
