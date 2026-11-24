//! What type checking found in a file's bodies, read for the language server: each expression
//! and pattern with its span in the file, the variables the code names, and the type a node
//! has, as the declaration's path of its head (edits.paths).

use stilt_db::{Database, Program, SourceFile};
use stilt_hir::hir::LocalId;
use stilt_syntax::{TextRange, TextSize};
use stilt_types::tast::walk::{catch_arms, iter, iter_block};
use stilt_types::tast::{Code, Definition, Expr, ExprKind, Pat, PatKind, StmtKind, TypedBody};
use stilt_types::ty::Ty;

/// A node of a typed body.
#[derive(Clone, Copy, Debug)]
pub(super) enum Node<'a> {
    Expr(&'a Expr),
    Pat(&'a Pat),
}

impl<'a> Node<'a> {
    pub(super) fn ty(self) -> &'a Ty {
        match self {
            Node::Expr(e) => &e.ty,
            Node::Pat(p) => &p.ty,
        }
    }
}

/// A body of a file, typed, with where it starts, which its spans are relative to.
pub(super) struct Body<'a> {
    pub start: TextSize,
    pub typed: &'a TypedBody,
}

/// The bodies of a file's module, in order.
pub(super) fn bodies(db: &Database, program: Program, file: SourceFile) -> Vec<Body<'_>> {
    let starts = stilt_hir::body_starts(db, program, file);
    (0..starts.len())
        .filter_map(|i| {
            let index = u32::try_from(i).ok()?;
            let typed = &stilt_types::infer_body(db, program, file, index).body;
            Some(Body {
                start: starts[i],
                typed,
            })
        })
        .collect()
}

/// The body that holds `offset`, if it has no error.
pub(super) fn body_at(
    db: &Database,
    program: Program,
    file: SourceFile,
    offset: TextSize,
) -> Option<Body<'_>> {
    let index = stilt_hir::body_at(db, program, file, offset)?;
    let typed = &stilt_types::infer_body(db, program, file, index).body;
    matches!(typed.code, Definition::Code(_)).then_some(Body {
        start: stilt_hir::body_starts(db, program, file)[index as usize],
        typed,
    })
}

impl<'a> Body<'a> {
    /// Every expression and pattern of the body, with its span in the file.
    pub(super) fn nodes(&self) -> Vec<(TextRange, Node<'a>)> {
        let Definition::Code(code) = &self.typed.code else {
            return Vec::new();
        };
        let mut patterns: Vec<&'a Pat> = Vec::new();
        let mut exprs: Vec<&'a Expr> = Vec::new();
        let mut stmt = |s: &'a stilt_types::tast::Stmt| {
            if let StmtKind::Let(b) | StmtKind::Var(b) = &s.kind {
                patterns.push(&b.pattern);
            }
        };
        let mut expr = |e: &'a Expr| exprs.push(e);
        match code {
            Code::Block(b) => iter_block(b, &mut stmt, &mut expr),
            Code::Expr(e) => iter(e, &mut stmt, &mut expr),
        }
        let mut found: Vec<(TextRange, Node<'a>)> = Vec::new();
        for e in exprs {
            found.push((e.at + self.start, Node::Expr(e)));
            patterns.extend(patterns_of(e));
        }
        let mut all = Vec::new();
        for p in patterns {
            subpatterns(p, &mut all);
        }
        found.extend(all.into_iter().map(|p| (p.at + self.start, Node::Pat(p))));
        found
    }

    /// The variables bound by `var`, which code may change, and the names of `when`s, writable
    /// as a `var` is (shared.when).
    pub(super) fn mutable(&self) -> Vec<LocalId> {
        let Definition::Code(code) = &self.typed.code else {
            return Vec::new();
        };
        let mut bound: Vec<&Pat> = Vec::new();
        let mut held: Vec<LocalId> = Vec::new();
        let mut stmt = |s: &'a stilt_types::tast::Stmt| {
            if let StmtKind::Var(b) = &s.kind {
                bound.push(&b.pattern);
            }
        };
        let mut expr = |e: &'a Expr| {
            if let ExprKind::When(names, _) = &e.kind {
                held.extend(names.iter().map(|(_, place)| *place));
            }
        };
        match code {
            Code::Block(b) => iter_block(b, &mut stmt, &mut expr),
            Code::Expr(e) => iter(e, &mut stmt, &mut expr),
        }
        let mut all = Vec::new();
        for p in bound {
            subpatterns(p, &mut all);
        }
        all.iter()
            .filter_map(|p| match p.kind {
                PatKind::Bind(v) => Some(v),
                _ => None,
            })
            .chain(held)
            .collect()
    }
}

/// The nodes of the body around `offset` that hold it, the smallest first.
pub(super) fn around(
    db: &Database,
    program: Program,
    file: SourceFile,
    offset: TextSize,
) -> Vec<(TextRange, Node<'_>)> {
    let Some(body) = body_at(db, program, file, offset) else {
        return Vec::new();
    };
    let mut found: Vec<(TextRange, Node<'_>)> = body
        .nodes()
        .into_iter()
        .filter(|(r, _)| r.contains_inclusive(offset))
        .collect();
    found.sort_by_key(|(r, _)| r.len());
    found
}

/// The node of the body around `range` whose span is `range`.
pub(super) fn node_at(
    db: &Database,
    program: Program,
    file: SourceFile,
    range: TextRange,
) -> Option<Node<'_>> {
    around(db, program, file, range.start())
        .into_iter()
        .find(|(r, _)| *r == range)
        .map(|(_, n)| n)
}

/// The path of the declaration of a type's head, as `main.Point` or `std.prelude.List`.
pub(super) fn head(ty: &Ty) -> Option<String> {
    match ty {
        Ty::Con(item, _) => Some(format!("{}.{}", item.home, item.name)),
        _ => None,
    }
}

/// The patterns that an expression holds directly: a closure's parameters, the arms of a
/// `match` or a `catch`, and the pattern of a `for` loop or an `if let`.
fn patterns_of(e: &Expr) -> Vec<&Pat> {
    match &e.kind {
        ExprKind::Closure(params, _) => params.iter().collect(),
        ExprKind::Match(_, arms) => arms.iter().map(|a| &a.pattern).collect(),
        ExprKind::Try(_, catch) => catch_arms(catch.as_ref())
            .iter()
            .map(|a| &a.pattern)
            .collect(),
        ExprKind::For(p, ..) | ExprKind::IfLet(p, ..) => vec![p],
        _ => Vec::new(),
    }
}

/// A pattern and every pattern inside it.
fn subpatterns<'a>(p: &'a Pat, out: &mut Vec<&'a Pat>) {
    out.push(p);
    match &p.kind {
        PatKind::Variant(_, ps) | PatKind::Tuple(ps) | PatKind::Or(ps) | PatKind::List(ps, _) => {
            for q in ps {
                subpatterns(q, out);
            }
        }
        PatKind::Record(fields) => {
            for (_, q) in fields {
                subpatterns(q, out);
            }
        }
        PatKind::Wild
        | PatKind::Bind(_)
        | PatKind::Int(_)
        | PatKind::Str(_)
        | PatKind::Bool(_)
        | PatKind::Const(_)
        | PatKind::Error => {}
    }
}
