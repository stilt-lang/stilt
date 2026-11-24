//! A walk over the expressions and patterns of a body, in source order. A visitor overrides
//! what it looks for, and walks on through the rest with the `walk_` functions.

use super::{
    Arm, Block, Body, BodyValue, Expr, ExprKind, Iterable, Pat, PatKind, Segment, StmtKind,
};

/// What a walk does at each expression and pattern.
pub trait Visitor {
    /// Visits an expression; walks into its parts unless overridden.
    fn expr(&mut self, e: &Expr) {
        walk_expr(self, e);
    }

    /// Visits a pattern; walks into its parts unless overridden.
    fn pat(&mut self, p: &Pat) {
        walk_pat(self, p);
    }
}

/// Visits every expression and pattern of a body, in source order.
pub fn walk_body<V: Visitor + ?Sized>(v: &mut V, body: &Body) {
    match &body.value {
        BodyValue::Block(block) => walk_block(v, block),
        BodyValue::Expr(e) | BodyValue::Property(e, _) => v.expr(e),
    }
}

/// The statements of a block. A binding's value comes before its pattern.
pub fn walk_block<V: Visitor + ?Sized>(v: &mut V, block: &Block) {
    for stmt in block {
        match &stmt.kind {
            StmtKind::Let(b) | StmtKind::Var(b) => {
                v.expr(&b.value);
                v.pat(&b.pattern);
            }
            StmtKind::Assign(_, place, value) => {
                v.expr(place);
                v.expr(value);
            }
            StmtKind::Assert(e) | StmtKind::Yield(e) | StmtKind::Expr(e) => v.expr(e),
        }
    }
}

/// The expressions and patterns directly inside an expression.
pub fn walk_expr<V: Visitor + ?Sized>(v: &mut V, e: &Expr) {
    match &e.kind {
        ExprKind::Interpolated(segments) => walk_segments(v, segments),
        ExprKind::Tuple(es) | ExprKind::List(es) => walk_all(v, es),
        // A quote's splices are the code around it; what it writes is code of no body here.
        ExprKind::Quote(q) => walk_all(v, q.splices.iter().map(|s| &s.value)),
        ExprKind::Field(e, _)
        | ExprKind::Spread(e)
        | ExprKind::Unary(_, e)
        | ExprKind::Raise(e)
        | ExprKind::Return(Some(e))
        | ExprKind::Comptime(e)
        | ExprKind::Resume(Some(e)) => v.expr(e),
        ExprKind::Call(callee, args) => {
            v.expr(callee);
            walk_all(v, args.iter().map(|a| &a.value));
        }
        ExprKind::Index(a, b) | ExprKind::Binary(_, a, b) | ExprKind::Else(a, b) => {
            v.expr(a);
            v.expr(b);
        }
        ExprKind::Try(operand, arms) => walk_arms(v, operand, arms.iter().flatten()),
        ExprKind::Match(scrutinee, arms) => walk_arms(v, scrutinee, arms),
        ExprKind::Block(block) | ExprKind::Loop(block) => walk_block(v, block),
        ExprKind::If(cond, body, alt) => walk_conditional(v, cond, body, alt.as_deref()),
        ExprKind::IfLet(pattern, scrutinee, body, alt) => {
            v.expr(scrutinee);
            v.pat(pattern);
            walk_conditional_rest(v, body, alt.as_deref());
        }
        ExprKind::While(cond, body) => walk_conditional(v, cond, body, None),
        ExprKind::Struct(..)
        | ExprKind::Update(..)
        | ExprKind::Closure(..)
        | ExprKind::Handler(_)
        | ExprKind::With(..)
        | ExprKind::When(..) => walk_compound(v, e),
        ExprKind::For(pattern, iterable, body) => walk_for(v, pattern, iterable, body),
        ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Local(_)
        | ExprKind::Func(_)
        | ExprKind::Const(_)
        | ExprKind::Variant(_)
        | ExprKind::ValueParam(..)
        | ExprKind::Member(..)
        | ExprKind::Bound(_)
        | ExprKind::Perform(..)
        | ExprKind::Resume(None)
        | ExprKind::KeyRoot
        | ExprKind::Hole
        | ExprKind::Return(None)
        | ExprKind::Break
        | ExprKind::Continue
        | ExprKind::Error => {}
    }
}

/// The splices of an interpolated string.
fn walk_segments<V: Visitor + ?Sized>(v: &mut V, segments: &[Segment]) {
    for segment in segments {
        if let Segment::Splice(e, _) = segment {
            v.expr(e);
        }
    }
}

/// A struct literal's fields, an update's base and fields, a closure's parameters and body, a
/// handler literal's bodies, a `with`'s handlers and block (handlers.handler-literals and
/// handlers.with), and a `when`'s handles and block (shared.when).
fn walk_compound<V: Visitor + ?Sized>(v: &mut V, e: &Expr) {
    match &e.kind {
        ExprKind::Closure(params, body) => {
            for param in params {
                v.pat(&param.pattern);
            }
            v.expr(body);
        }
        ExprKind::Struct(_, fields) => walk_all(v, fields.iter().map(|f| &f.value)),
        ExprKind::Update(_, base, fields) => {
            v.expr(base);
            walk_all(v, fields.iter().map(|f| &f.value));
        }
        ExprKind::Handler(h) => {
            for op in &h.ops {
                walk_block(v, &op.body);
            }
        }
        ExprKind::With(handlers, body) => {
            walk_all(v, handlers);
            walk_block(v, body);
        }
        ExprKind::When(held, body) => {
            walk_all(v, held.iter().map(|h| &h.handle));
            walk_block(v, body);
        }
        _ => {}
    }
}

fn walk_all<'e, V: Visitor + ?Sized>(v: &mut V, es: impl IntoIterator<Item = &'e Expr>) {
    for e in es {
        v.expr(e);
    }
}

/// A `match` or a `try`: what it inspects, then each arm's pattern, guard and body.
fn walk_arms<'a, V: Visitor + ?Sized>(
    v: &mut V,
    e: &Expr,
    arms: impl IntoIterator<Item = &'a Arm>,
) {
    v.expr(e);
    for arm in arms {
        v.pat(&arm.pattern);
        if let Some(guard) = &arm.guard {
            v.expr(guard);
        }
        v.expr(&arm.body);
    }
}

/// An `if` or a `while`: its condition, its block, and what follows an `if`'s `else`.
fn walk_conditional<V: Visitor + ?Sized>(v: &mut V, cond: &Expr, body: &Block, alt: Option<&Expr>) {
    v.expr(cond);
    walk_conditional_rest(v, body, alt);
}

/// The block of an `if`, a `while` or an `if let`, then its `else`.
fn walk_conditional_rest<V: Visitor + ?Sized>(v: &mut V, body: &Block, alt: Option<&Expr>) {
    walk_block(v, body);
    if let Some(alt) = alt {
        v.expr(alt);
    }
}

/// A `for` loop: its iterable, then its pattern and body.
fn walk_for<V: Visitor + ?Sized>(v: &mut V, pattern: &Pat, iterable: &Iterable, body: &Block) {
    match iterable {
        Iterable::Iter(e) => v.expr(e),
        Iterable::Range(start, end, _) => {
            v.expr(start);
            v.expr(end);
        }
    }
    v.pat(pattern);
    walk_block(v, body);
}

/// The patterns directly inside a pattern.
pub fn walk_pat<V: Visitor + ?Sized>(v: &mut V, p: &Pat) {
    match &p.kind {
        PatKind::Tuple(ps)
        | PatKind::Variant(_, ps)
        | PatKind::Bare(_, ps, _)
        | PatKind::List(ps, _)
        | PatKind::Or(ps) => {
            for q in ps {
                v.pat(q);
            }
        }
        PatKind::Record(_, fields, _) | PatKind::AnonRecord(fields, _) => {
            for field in fields {
                v.pat(&field.pattern);
            }
        }
        PatKind::Wild
        | PatKind::Bind(_)
        | PatKind::Int(_)
        | PatKind::Str(_)
        | PatKind::Bool(_)
        | PatKind::Const(_)
        | PatKind::AssocConst(..)
        | PatKind::Error => {}
    }
}
