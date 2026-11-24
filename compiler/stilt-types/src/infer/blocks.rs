//! Blocks, and the statements in them: bindings and assignments.

use stilt_diag::{Edit, Fix, codes};
use stilt_hir::hir::{self, BinaryOp, StmtKind};
use stilt_syntax::TextRange;

use super::fields::{checked_place, not_a_place};
use super::{Cx, Leading, Receiver, Rule, State, UnitSite};
use crate::tast;
use crate::ty::Ty;

impl State<'_> {
    /// patterns.let-else: a binding whose value is an `else` is a let-else when its pattern is
    /// refutable, its names written without a module read against the annotation's type, or else
    /// the type of the expression before `else` (patterns.variants-by-type), and otherwise the
    /// `Option` fallback.
    fn binding(&mut self, cx: &mut Cx, b: &hir::Binding) -> tast::Binding {
        let annotation = b.annotation.as_ref().map(|a| self.of_hir(a));
        let hir::ExprKind::Else(source, otherwise) = &b.value.kind else {
            let v = self.infer_checked(cx, annotation.as_ref(), &b.value);
            return self.plain(cx, b, annotation.as_ref(), v);
        };
        let inferred = match &annotation {
            Some(_) => None,
            None => Some(self.infer(cx, None, source)),
        };
        let against = annotation.as_ref().or(inferred.as_ref().map(|x| &x.ty));
        if self.irrefutable(&b.pattern, against) {
            let v = match inferred {
                Some(x) => self.option_fallback(cx, b.value.at, source, x, otherwise),
                None => self.infer_checked(cx, annotation.as_ref(), &b.value),
            };
            return self.plain(cx, b, annotation.as_ref(), v);
        }
        let v = match inferred {
            Some(x) => x,
            None => self.infer_checked(cx, annotation.as_ref(), source),
        };
        let pattern = self.pattern(cx, &b.pattern, annotation.as_ref().unwrap_or(&v.ty));
        let o = self.infer(cx, None, otherwise);
        if !(self.is_never(&o.ty) || *self.table.resolve(&o.ty) == Ty::Error) {
            let message = format!(
                "the `else` branch of a let-else must have type `Never`, not `{}`",
                self.show(&o.ty)
            );
            self.error(codes::E0311, otherwise.at, message);
        }
        tast::Binding {
            pattern,
            value: v,
            otherwise: Some(Box::new(o)),
        }
    }

    /// A binding without let-else, whose pattern must be irrefutable once checked
    /// (patterns.irrefutable-positions).
    fn plain(
        &mut self,
        cx: &mut Cx,
        b: &hir::Binding,
        annotation: Option<&Ty>,
        v: tast::Expr,
    ) -> tast::Binding {
        let pattern = self.pattern(cx, &b.pattern, annotation.unwrap_or(&v.ty));
        if !self.irrefutable(&b.pattern, None) {
            self.refutable_binding(b);
        }
        tast::Binding {
            pattern,
            value: v,
            otherwise: None,
        }
    }

    /// A refutable pattern without a let-else (patterns.let-else). When the value is a `try` whose
    /// operand ends in an `else`, that `else` belongs to the operand, so the binding is no
    /// let-else, and parentheses around the `try` make it one.
    fn refutable_binding(&mut self, b: &hir::Binding) {
        let hir::ExprKind::Try(operand, None) = &b.value.kind else {
            return self.require_irrefutable(&b.pattern);
        };
        let hir::ExprKind::Else(source, _) = &operand.kind else {
            return self.require_irrefutable(&b.pattern);
        };
        let message = "this pattern can fail to match: the `else` is part of the operand of \
                       `try`, so this isn't a let-else";
        let wrap = Fix::new(
            "put the `try` in parentheses",
            vec![
                Edit::insert(b.value.at.start(), "("),
                Edit::insert(source.at.end(), ")"),
            ],
        );
        self.error_fixed(codes::E0321, b.pattern.at, message.to_owned(), vec![wrap]);
    }

    fn assignment(
        &mut self,
        cx: &mut Cx,
        op: Option<BinaryOp>,
        place: &hir::Expr,
        value: &hir::Expr,
    ) -> tast::StmtKind {
        let mut p = self.infer(cx, None, place);
        // What isn't a place has no type that the value must fit (errors.error-type).
        if !checked_place(place, &p) {
            let message = "only a variable, a field or an element can be assigned to";
            self.error(codes::E0401, place.at, message.to_owned());
            p.ty = Ty::Error;
        } else if let Some(reason) = not_a_place(&p) {
            let message = format!("{reason}, so it can't be assigned to");
            self.error(codes::E0401, place.at, message);
            p.ty = Ty::Error;
        }
        let v = if let Some(BinaryOp::Shl | BinaryOp::Shr) = op {
            self.amount_of(cx, &p.ty, value)
        } else {
            // meta.leaving-arm: a value assigned to a variable declared outside an arm leaves it.
            let depth = self.place_depth(&p);
            self.check_leaving(cx, (&p.ty, depth, "leave it"), value)
        };
        match op {
            None => {}
            Some(BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem) => {
                self.operator(&p.ty, Rule::Numeric, place.at);
            }
            Some(_) => {
                self.operator(&p.ty, Rule::Integer, place.at);
            }
        }
        tast::StmtKind::Assign(op, p, v)
    }

    fn stmt(&mut self, cx: &mut Cx, s: &hir::Stmt, next: Option<&hir::Stmt>) -> tast::StmtKind {
        let wrap = match &s.kind {
            StmtKind::Let(b) | StmtKind::Var(b) => b.value.at,
            _ => s.at,
        };
        let outer = self.wrap.replace(wrap);
        let checked = self.stmt_kind(cx, s, next);
        self.wrap = outer;
        checked
    }

    fn stmt_kind(
        &mut self,
        cx: &mut Cx,
        s: &hir::Stmt,
        next: Option<&hir::Stmt>,
    ) -> tast::StmtKind {
        match &s.kind {
            StmtKind::Expr(e) => {
                let v = self.infer(cx, None, e);
                // expressions.statements
                if !resumes(e) {
                    let site = UnitSite::Statement(leading_closure(next), receiver(e));
                    self.units.push((v.ty.clone(), site, s.at));
                }
                tast::StmtKind::Expr(v)
            }
            StmtKind::Let(b) => tast::StmtKind::Let(self.binding(cx, b)),
            StmtKind::Var(b) => {
                if let hir::PatKind::Bind(v) = b.pattern.kind {
                    self.modifiable.push(v);
                }
                tast::StmtKind::Var(self.binding(cx, b))
            }
            StmtKind::Assign(op, place, value) => self.assignment(cx, *op, place, value),
            StmtKind::Assert(e) => tast::StmtKind::Assert(self.check(cx, &Ty::bool(), e)),
            StmtKind::Yield(e) => self.yield_stmt(cx, s.at, e),
        }
    }

    /// projections.yield: `yield e` hands the caller a place of the projection's type, or a view
    /// that a temporary holds.
    fn yield_stmt(&mut self, cx: &mut Cx, at: TextRange, operand: &hir::Expr) -> tast::StmtKind {
        let Some(ty) = cx.yields.clone() else {
            let message = "`yield` belongs in a projection's body, a function whose result is \
                           written `inout T`";
            self.error(codes::E0425, at, message.to_owned());
            return tast::StmtKind::Yield(self.abandon(cx, operand));
        };
        let mut v = self.infer(cx, Some(&ty), operand);
        if checked_place(operand, &v) && not_a_place(&v).is_none() {
            // A place is handed to the caller, so its type is the result's exactly.
            self.expect(operand.at, &ty, &v.ty);
        } else if !self.resolved(&v.ty).is_view() {
            let message = "only a variable, a field or an element can be yielded";
            self.error(codes::E0401, operand.at, message.to_owned());
            v.ty = Ty::Error;
        }
        tast::StmtKind::Yield(v)
    }

    /// A block and its type. Checked against an expected type, a block has that type: its
    /// final expression is checked against it, and a block without one has type `()`, which
    /// must fit it, as reported at `at`.
    pub(super) fn block_expr(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        expected: Option<&Ty>,
        stmts: &[hir::Stmt],
    ) -> (tast::Block, Ty) {
        let mut block = Vec::new();
        let last_expr = match stmts.last() {
            Some(hir::Stmt {
                kind: StmtKind::Expr(e),
                ..
            }) => Some(e),
            _ => None,
        };
        let leading = if last_expr.is_some() {
            &stmts[..stmts.len() - 1]
        } else {
            stmts
        };
        for (i, s) in leading.iter().enumerate() {
            let kind = self.stmt(cx, s, stmts.get(i + 1));
            block.push(tast::Stmt { kind, at: s.at });
        }
        let ty = if let Some(e) = last_expr {
            let outer = self.wrap.replace(e.at);
            let v = self.infer_checked(cx, expected, e);
            self.wrap = outer;
            let ty = expected.cloned().unwrap_or_else(|| v.ty.clone());
            block.push(tast::Stmt {
                kind: tast::StmtKind::Expr(v),
                at: e.at,
            });
            ty
        } else {
            if let Some(t) = expected {
                self.subsume(at, t, &Ty::unit());
            }
            expected.cloned().unwrap_or_else(Ty::unit)
        };
        (block, ty)
    }

    /// A loop's body, whose value is discarded, so that its last expression statement, like
    /// every other, must have type `()` or `Never` (expressions.statements).
    pub(super) fn loop_body(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        body: &[hir::Stmt],
    ) -> tast::Block {
        let (b, ty) = self.block_expr(cx, at, None, body);
        if let Some(hir::Stmt {
            kind: StmtKind::Expr(e),
            at,
        }) = body.last()
            && !resumes(e)
        {
            self.units.push((ty, UnitSite::Statement(None, None), *at));
        }
        b
    }
}

/// handlers.resuming: a body that resumes may go on, dropping what the rest of the block gave, so
/// a `resume` needs no `let _ =` as a statement.
fn resumes(e: &hir::Expr) -> bool {
    matches!(e.kind, hir::ExprKind::Resume(_))
}

/// The closure without parameters that a statement is, if it is one: lexical.terminator-insertion
/// makes a line that starts with `||` begin a closure, not continue the line before.
/// The local whose method the statement `e` calls, if it calls one of a local.
fn receiver(e: &hir::Expr) -> Option<Receiver> {
    let hir::ExprKind::Call(callee, _) = &e.kind else {
        return None;
    };
    match &callee.kind {
        hir::ExprKind::Field(base, _) => match base.kind {
            hir::ExprKind::Local(local) => Some(Receiver { local }),
            _ => None,
        },
        _ => None,
    }
}

fn leading_closure(next: Option<&hir::Stmt>) -> Option<Leading> {
    let hir::Stmt {
        kind: StmtKind::Expr(e),
        ..
    } = next?
    else {
        return None;
    };
    match &e.kind {
        hir::ExprKind::Closure(params, body) if params.is_empty() => Some(Leading {
            closure: e.at,
            operator: TextRange::new(e.at.start(), body.at.start()),
        }),
        _ => None,
    }
}
