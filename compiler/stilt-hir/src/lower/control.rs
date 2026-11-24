//! Control flow, blocks and statements (expressions.statements and expressions.block-value;
//! patterns.let-else).

use stilt_diag::codes;
use stilt_syntax::ast::{self, AstNode};
use stilt_syntax::text::string_value;
use stilt_syntax::{SyntaxKind as K, TextRange};

use super::patterns::Binder;
use super::poly::Spot;
use super::{Ctx, Resolver};
use crate::hir::{
    Arm, BinaryOp, Binding, Block, ClosureParam, ExprKind, Iterable, Mode, Stmt, StmtKind,
    UnsafeBlock,
};

impl Resolver<'_> {
    /// `unsafe because "reason" { … }` (c.unsafe-because): its block, which the body records as
    /// unsafe, with E0437 at a reason that holds only whitespace (lexical.whitespace).
    pub(super) fn unsafe_block(
        &mut self,
        ctx: &Ctx,
        u: &ast::UnsafeExpr,
        whole: TextRange,
    ) -> ExprKind {
        let reason = u.reason().map(|t| (string_value(&t), self.at_token(&t)));
        if let Some((text, at)) = &reason
            && text.chars().all(|c| matches!(c, ' ' | '\t' | '\n'))
        {
            let message = "this `unsafe` block gives no reason; say why its code is sound";
            self.error(codes::E0437, *at, message.to_owned());
        }
        let at = u.unsafe_token().map_or(whole, |t| self.at_token(&t));
        self.unsafe_blocks.push(UnsafeBlock {
            at,
            reason: reason.map(|(text, _)| text).unwrap_or_default(),
            whole,
        });
        ExprKind::Block(self.block(ctx, u.body()))
    }

    pub(super) fn try_expr(&mut self, ctx: &Ctx, t: &ast::TryExpr) -> ExprKind {
        let operand = self.boxed(ctx, t.expr());
        let arms = t
            .catch_clause()
            .map(|c| c.arms().map(|a| self.arm(ctx, &a)).collect());
        ExprKind::Try(operand, arms)
    }

    /// A closure, whose body `break` and `continue` can't leave (expressions.break-and-continue).
    pub(super) fn closure(&mut self, ctx: &Ctx, c: &ast::ClosureExpr) -> ExprKind {
        let mut b = Binder::default();
        let params = c
            .params()
            .map(|p| {
                let annotation = p.ty().map(|t| self.type_ref(ctx, t, Spot::Closure));
                let pattern = self.pattern(ctx, &mut b, p.pattern());
                ClosureParam {
                    mode: if p.is_inout() { Mode::Inout } else { Mode::Let },
                    pattern,
                    annotation,
                    at: self.at(p.syntax()),
                }
            })
            .collect();
        let depth = self.scope.len();
        self.bring_into_scope(&b);
        let inner = Ctx {
            in_loop: false,
            ..ctx.clone()
        };
        let body = self.boxed(&inner, c.body());
        self.scope.truncate(depth);
        ExprKind::Closure(params, body)
    }

    pub(super) fn match_expr(&mut self, ctx: &Ctx, m: &ast::MatchExpr) -> ExprKind {
        let scrutinee = self.boxed(ctx, m.scrutinee());
        ExprKind::Match(scrutinee, m.arms().map(|a| self.arm(ctx, &a)).collect())
    }

    pub(super) fn while_loop(&mut self, ctx: &Ctx, w: &ast::WhileExpr) -> ExprKind {
        let cond = self.boxed(ctx, w.condition());
        ExprKind::While(cond, self.block(&in_loop(ctx), w.body()))
    }

    pub(super) fn if_expr(&mut self, ctx: &Ctx, i: &ast::IfExpr) -> ExprKind {
        let cond = match i.bound_test() {
            Some(test) => Box::new(crate::hir::Expr {
                at: self.at(test.syntax()),
                kind: ExprKind::Bound(Box::new(self.bound_test(ctx, &test))),
            }),
            None => self.boxed(ctx, i.condition()),
        };
        if i.is_let() {
            return self.if_let(ctx, i, cond);
        }
        let body = self.block(ctx, i.then_block());
        let alt = i.else_branch().map(|e| Box::new(self.expr(ctx, &e)));
        ExprKind::If(cond, body, alt)
    }

    /// An `if let`, whose pattern's variables are in scope in its first block only
    /// (expressions.if-let and expressions.scope).
    fn if_let(&mut self, ctx: &Ctx, i: &ast::IfExpr, scrutinee: Box<crate::hir::Expr>) -> ExprKind {
        let mut b = Binder::default();
        let pattern = self.pattern(ctx, &mut b, i.pattern());
        let depth = self.scope.len();
        self.bring_into_scope(&b);
        let body = self.block(ctx, i.then_block());
        self.scope.truncate(depth);
        let alt = i.else_branch().map(|e| Box::new(self.expr(ctx, &e)));
        ExprKind::IfLet(Box::new(pattern), scrutinee, body, alt)
    }

    /// A `for` loop, whose pattern's variables are in scope in its body.
    pub(super) fn for_loop(&mut self, ctx: &Ctx, f: &ast::ForExpr) -> ExprKind {
        let iterable = match f.iterable() {
            Some(ast::Iterable::Range(r)) => {
                let start = self.opt_expr(ctx, r.start());
                let end = self.opt_expr(ctx, r.end());
                Iterable::Range(start, end, r.is_inclusive())
            }
            Some(ast::Iterable::Expr(e)) => Iterable::Iter(self.expr(ctx, &e)),
            None => Iterable::Iter(self.opt_expr(ctx, None)),
        };
        let mut b = Binder::default();
        let pattern = self.pattern(ctx, &mut b, f.pattern());
        let depth = self.scope.len();
        self.bring_into_scope(&b);
        let body = self.block(&in_loop(ctx), f.body());
        self.scope.truncate(depth);
        ExprKind::For(Box::new(pattern), Box::new(iterable), body)
    }
}

impl Resolver<'_> {
    /// expressions.break-and-continue.
    pub(super) fn jump(
        &mut self,
        ctx: &Ctx,
        at: TextRange,
        keyword: &str,
        kind: ExprKind,
    ) -> ExprKind {
        if ctx.in_loop {
            kind
        } else {
            let message = format!("`{keyword}` is outside the body of every loop");
            self.error(codes::E0216, at, message);
            ExprKind::Error
        }
    }

    pub(super) fn arm(&mut self, ctx: &Ctx, a: &ast::Arm) -> Arm {
        let mut b = Binder::default();
        let pattern = self.pattern(ctx, &mut b, a.pattern());
        let depth = self.scope.len();
        self.bring_into_scope(&b);
        let guard = a.guard().map(|g| self.opt_expr(ctx, g.expr()));
        let because = a
            .because()
            .and_then(|b| b.reason())
            .map(|reason| (string_value(&reason), self.at_token(&reason)));
        let body = self.opt_expr(ctx, a.body());
        self.scope.truncate(depth);
        Arm {
            pattern,
            guard: guard.map(Box::new),
            because,
            body,
        }
    }

    pub(super) fn block(&mut self, ctx: &Ctx, block: Option<ast::Block>) -> Block {
        let depth = self.scope.len();
        let stmts = block
            .into_iter()
            .flat_map(|b| b.stmts())
            .map(|s| self.stmt(ctx, &s))
            .collect();
        self.scope.truncate(depth);
        stmts
    }

    /// Resolves a statement. The variables of a `let` or `var` are in scope after the
    /// statement, not in its value (patterns.let-else), until the end of the block.
    pub(super) fn stmt(&mut self, ctx: &Ctx, s: &ast::Stmt) -> Stmt {
        let at = self.at(s.syntax());
        let kind = match s {
            ast::Stmt::LetStmt(l) => {
                StmtKind::Let(self.binding(ctx, l.pattern(), l.ty(), l.value()))
            }
            ast::Stmt::VarStmt(v) => {
                StmtKind::Var(self.binding(ctx, v.pattern(), v.ty(), v.value()))
            }
            ast::Stmt::AssignStmt(a) => {
                let place = self.opt_expr(ctx, a.place());
                let value = self.opt_expr(ctx, a.value());
                let op = a.op().and_then(|t| compound_op(t.kind()));
                StmtKind::Assign(op, place, value)
            }
            ast::Stmt::AssertStmt(a) => StmtKind::Assert(self.opt_expr(ctx, a.expr())),
            ast::Stmt::YieldStmt(y) => StmtKind::Yield(self.opt_expr(ctx, y.expr())),
            ast::Stmt::ExprStmt(x) => StmtKind::Expr(self.opt_expr(ctx, x.expr())),
        };
        Stmt { kind, at }
    }

    pub(super) fn binding(
        &mut self,
        ctx: &Ctx,
        pattern: Option<ast::Pattern>,
        annotation: Option<ast::Type>,
        value: Option<ast::Expr>,
    ) -> Binding {
        let value = self.opt_expr(ctx, value);
        let annotation = annotation.map(|t| self.type_ref(ctx, t, Spot::Local));
        let mut b = Binder::default();
        let pattern = self.pattern(ctx, &mut b, pattern);
        self.bring_into_scope(&b);
        Binding {
            pattern,
            annotation: annotation.map(Box::new),
            value,
        }
    }
}

pub(super) fn in_loop(ctx: &Ctx) -> Ctx {
    Ctx {
        in_loop: true,
        ..ctx.clone()
    }
}

/// The operator of a compound assignment, or `None` for `=`.
fn compound_op(kind: K) -> Option<BinaryOp> {
    use BinaryOp as B;
    Some(match kind {
        K::PLUS_EQ => B::Add,
        K::MINUS_EQ => B::Sub,
        K::STAR_EQ => B::Mul,
        K::SLASH_EQ => B::Div,
        K::PERCENT_EQ => B::Rem,
        K::PLUS_PERCENT_EQ => B::AddWrap,
        K::MINUS_PERCENT_EQ => B::SubWrap,
        K::STAR_PERCENT_EQ => B::MulWrap,
        K::AMP_EQ => B::BitAnd,
        K::PIPE_EQ => B::BitOr,
        K::CARET_EQ => B::BitXor,
        K::SHL_EQ => B::Shl,
        K::SHR_EQ => B::Shr,
        _ => return None,
    })
}
