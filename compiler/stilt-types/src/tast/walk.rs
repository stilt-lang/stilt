//! Traversals of typed bodies, shared by the later phases.

use super::{Arm, Block, Catch, Expr, ExprKind, Iterable, Segment, Stmt, StmtKind};

/// What an expression holds directly.
#[derive(Clone, Copy, Debug)]
pub enum Part<'a> {
    /// An expression.
    Expr(&'a Expr),
    /// A block.
    Block(&'a Block),
}

fn arm_parts(a: &Arm) -> impl Iterator<Item = Part<'_>> {
    a.guard
        .as_deref()
        .into_iter()
        .chain([&a.body])
        .map(Part::Expr)
}

/// The arms of a `catch`, if there is one.
#[must_use]
pub fn catch_arms(c: Option<&Catch>) -> &[Arm] {
    c.map_or(&[], |c| c.arms.as_slice())
}

/// The expressions and blocks directly inside an expression, in the order they are written:
/// its operands and arguments, its blocks, and the guards and bodies of its arms.
#[must_use]
pub fn parts(e: &Expr) -> Vec<Part<'_>> {
    fn exprs(es: &[Expr]) -> Vec<Part<'_>> {
        es.iter().map(Part::Expr).collect()
    }
    match &e.kind {
        ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Local(_)
        | ExprKind::Constant(_)
        | ExprKind::ValueParam(_)
        | ExprKind::Reflect(..)
        | ExprKind::Bound(..)
        | ExprKind::MemberConstant(..)
        | ExprKind::Callee(..)
        | ExprKind::Constructor(..)
        | ExprKind::Break
        | ExprKind::Continue
        | ExprKind::Hole
        | ExprKind::Error => Vec::new(),
        ExprKind::Interpolated(segments) => segments
            .iter()
            .filter_map(|s| match s {
                Segment::Text(_) => None,
                Segment::Splice(e, _) => Some(Part::Expr(e)),
            })
            .collect(),
        ExprKind::Construct(_, _, es) | ExprKind::Tuple(es) | ExprKind::List(es) => exprs(es),
        ExprKind::Quote(q) => q.splices.iter().map(|s| Part::Expr(&s.value)).collect(),
        ExprKind::Record(_, _, fields) => fields.iter().map(|(_, e)| Part::Expr(e)).collect(),
        ExprKind::Update(base, fields) => std::iter::once(Part::Expr(base))
            .chain(fields.iter().map(|(_, e)| Part::Expr(e)))
            .collect(),
        ExprKind::Spread(s) => vec![Part::Expr(&s.body)],
        ExprKind::Field(e, _)
        | ExprKind::TupleField(e, _)
        | ExprKind::Instantiate(e, _)
        | ExprKind::Unary(_, e)
        | ExprKind::Raise(e) => vec![Part::Expr(e)],
        ExprKind::Call(_, _, args, _) | ExprKind::Project(_, _, args, _) => {
            args.iter().map(|a| Part::Expr(&a.value)).collect()
        }
        ExprKind::CallValue(f, args) => std::iter::once(Part::Expr(f))
            .chain(args.iter().map(|a| Part::Expr(&a.value)))
            .collect(),
        ExprKind::Index(a, b) | ExprKind::Binary(_, a, b) | ExprKind::Else(a, b) => {
            vec![Part::Expr(a), Part::Expr(b)]
        }
        ExprKind::Return(e) | ExprKind::Resume(e) => e.iter().map(|e| Part::Expr(e)).collect(),
        ExprKind::Closure(_, body) => vec![Part::Expr(body)],
        ExprKind::Handler(h) => h.ops.iter().map(|(_, e)| Part::Expr(e)).collect(),
        ExprKind::With(h, _, _, b) => vec![Part::Expr(h), Part::Block(b)],
        ExprKind::When(held, b) => held
            .iter()
            .map(|(h, _)| Part::Expr(h))
            .chain([Part::Block(b)])
            .collect(),
        _ => control_parts(e),
    }
}

/// The parts of the forms that hold blocks or arms.
fn control_parts(e: &Expr) -> Vec<Part<'_>> {
    match &e.kind {
        ExprKind::Try(operand, catch) => std::iter::once(Part::Expr(operand))
            .chain(catch_arms(catch.as_ref()).iter().flat_map(arm_parts))
            .collect(),
        ExprKind::Block(b) | ExprKind::Loop(b) => vec![Part::Block(b)],
        ExprKind::If(c, b, alt) | ExprKind::IfLet(_, c, b, alt) => [Part::Expr(c), Part::Block(b)]
            .into_iter()
            .chain(alt.iter().map(|e| Part::Expr(e)))
            .collect(),
        ExprKind::Match(scrutinee, arms) => std::iter::once(Part::Expr(scrutinee))
            .chain(arms.iter().flat_map(arm_parts))
            .collect(),
        ExprKind::While(c, b) => vec![Part::Expr(c), Part::Block(b)],
        ExprKind::For(_, iterable, b) => match &**iterable {
            Iterable::Iter(source) => vec![Part::Expr(source), Part::Block(b)],
            Iterable::Range(a, z, _) => vec![Part::Expr(a), Part::Expr(z), Part::Block(b)],
        },
        _ => Vec::new(),
    }
}

/// The expressions directly inside a statement, in order.
#[must_use]
pub fn stmt_exprs(s: &Stmt) -> Vec<&Expr> {
    match &s.kind {
        StmtKind::Let(b) | StmtKind::Var(b) => std::iter::once(&b.value)
            .chain(b.otherwise.as_deref())
            .collect(),
        StmtKind::Assign(_, place, value) => vec![place, value],
        StmtKind::Assert(e) | StmtKind::Yield(e) | StmtKind::Expr(e) => vec![e],
    }
}

/// The expressions directly inside a block's statements, in order.
#[must_use]
pub fn block_exprs(b: &Block) -> Vec<&Expr> {
    b.iter().flat_map(stmt_exprs).collect()
}

/// The expressions directly inside an expression or its blocks, in order.
#[must_use]
pub fn children(e: &Expr) -> Vec<&Expr> {
    parts(e)
        .into_iter()
        .flat_map(|p| match p {
            Part::Expr(e) => vec![e],
            Part::Block(b) => block_exprs(b),
        })
        .collect()
}

/// Applies `f` to `e` and to every expression inside it, each before the expressions inside
/// it, in the order they are written, closures included, and `stmt` to every statement on the
/// way.
pub fn iter<'a>(e: &'a Expr, stmt: &mut dyn FnMut(&'a Stmt), f: &mut dyn FnMut(&'a Expr)) {
    f(e);
    for part in parts(e) {
        match part {
            Part::Expr(e) => iter(e, stmt, f),
            Part::Block(b) => iter_block(b, stmt, f),
        }
    }
}

/// [`iter`] on each statement of a block, `stmt` applied to each statement first.
pub fn iter_block<'a>(b: &'a Block, stmt: &mut dyn FnMut(&'a Stmt), f: &mut dyn FnMut(&'a Expr)) {
    for s in b {
        stmt(s);
        for e in stmt_exprs(s) {
            iter(e, stmt, f);
        }
    }
}

/// Applies `f` to every expression of a block, as [`iter_block`] does.
pub fn exprs_of_block<'a>(b: &'a Block, f: &mut dyn FnMut(&'a Expr)) {
    iter_block(b, &mut |_| {}, f);
}

/// Whether the expression, or an expression inside it, satisfies the predicate.
#[must_use]
pub fn exists(e: &Expr, p: &dyn Fn(&Expr) -> bool) -> bool {
    p(e) || children(e).into_iter().any(|e| exists(e, p))
}
