//! What the code names at a position of a file, for the language server's hovers and
//! definitions (goal one-engine): a local variable with its inferred type and its binding, a
//! function or a method that the code calls or names, by the path of its declaration (edits.paths,
//! edits.paths), a field it reads, with its type, the type of a variant that a pattern names, as
//! checking resolved it (patterns.variants-by-type), or an operation that it performs
//! (handlers.performing-operation).

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::hir::{GenericId, LocalId, Name};
use stilt_hir::{body_at, body_starts, module_body};
use stilt_syntax::{TextRange, TextSize};

use crate::queries::{generic_name, infer_body};
use crate::tast::walk::{iter, iter_block};
use crate::tast::{Callee, Code, Definition, Expr, ExprKind, Pat, PatKind, Stmt, StmtKind};
use crate::ty::{Table, Ty};

/// What the code names at a position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Named {
    /// A local variable, with its type as a program writes it, and where its binding is in
    /// its file.
    Local {
        /// Its name.
        name: Name,
        /// Its type, as a program writes it.
        ty: String,
        /// Where its binding is in its file.
        bound: TextRange,
    },
    /// A function or a method that the code calls or names, by the path of its declaration.
    Function(String),
    /// A field that the code reads, with its type.
    Field {
        /// Its name.
        name: Name,
        /// Its type, as a program writes it.
        ty: String,
    },
    /// The type of a variant that a pattern names, by the path of its declaration.
    Variant(String),
    /// An operation that the code performs, by the path of its effect's declaration and its
    /// name (handlers.performing-operation).
    Operation {
        /// The path of its effect's declaration.
        effect: String,
        /// Its name.
        name: Name,
    },
}

/// The innermost thing that the code of a body names at `offset` of `file`, if the body that
/// holds the offset has no error and names something there.
#[must_use]
pub fn named_at(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    offset: TextSize,
) -> Option<Named> {
    let index = body_at(db, program, file, offset)?;
    let start = body_starts(db, program, file)[index as usize];
    let typed = &infer_body(db, program, file, index).body;
    let Definition::Code(code) = &typed.code else {
        return None;
    };
    let at = offset - start;
    let found = innermost(code, at)?;
    let names = |id: &GenericId| *generic_name(db, program, id.clone());
    let show = |t: &Ty| Table::default().show(t, &names);
    let local = |v: LocalId, ty: &Ty| {
        let hir = module_body(db, program, file, index);
        let bound = hir.locals.get(v.0 as usize)?.at + start;
        Some(Named::Local {
            name: *typed.locals.get(v.0 as usize)?,
            ty: show(ty),
            bound,
        })
    };
    match found {
        Node::Bind(v, ty) => local(v, ty),
        Node::Variant(Ty::Con(owner, _)) => {
            Some(Named::Variant(format!("{}.{}", owner.home, owner.name)))
        }
        Node::Variant(_) => None,
        Node::Expr(e) => match &e.kind {
            ExprKind::Local(v) => local(*v, &e.ty),
            ExprKind::Call(Callee::Operation(effect, name), ..) => Some(Named::Operation {
                effect: format!("{}.{}", effect.home, effect.name),
                name: *name,
            }),
            ExprKind::Call(callee, ..)
            | ExprKind::Project(callee, ..)
            | ExprKind::Callee(callee, _) => Some(Named::Function(path(callee))),
            ExprKind::Field(_, name) => Some(Named::Field {
                name: *name,
                ty: show(&e.ty),
            }),
            _ => None,
        },
    }
}

/// The path of a callee's declaration (edits.paths): a function's, an inherent member's
/// in its type's home module, or a trait method's in its trait.
fn path(callee: &Callee) -> String {
    match callee {
        Callee::Function(item) => format!("{}.{}", item.home, item.name),
        Callee::Member(owner, name) => format!("{}.{}.{name}", owner.home, owner.name),
        Callee::TraitMethod(t, name, _) | Callee::Operation(t, name) => {
            format!("{}.{}.{name}", t.home, t.name)
        }
    }
}

/// A node of a typed body: an expression, a variable a pattern binds, with its type, or a
/// pattern of a variant, with the variant's type.
#[derive(Clone, Copy)]
enum Node<'a> {
    Expr(&'a Expr),
    Bind(LocalId, &'a Ty),
    Variant(&'a Ty),
}

/// The smallest node of `code` whose span holds `at`.
fn innermost<'a>(code: &'a Code, at: TextSize) -> Option<Node<'a>> {
    let mut best: Option<(TextRange, Node<'a>)> = None;
    let mut consider = |range: TextRange, node| {
        if range.contains_inclusive(at) && best.is_none_or(|(b, _)| range.len() <= b.len()) {
            best = Some((range, node));
        }
    };
    let mut patterns: Vec<&'a Pat> = Vec::new();
    let mut stmt = |s: &'a Stmt| {
        if let StmtKind::Let(b) | StmtKind::Var(b) = &s.kind {
            patterns.push(&b.pattern);
        }
    };
    let mut exprs: Vec<&'a Expr> = Vec::new();
    let mut expr = |e: &'a Expr| exprs.push(e);
    match code {
        Code::Block(b) => iter_block(b, &mut stmt, &mut expr),
        Code::Expr(e) => iter(e, &mut stmt, &mut expr),
    }
    for e in &exprs {
        consider(e.at, Node::Expr(e));
        patterns.extend(patterns_of(e));
    }
    let mut named = Vec::new();
    for p in patterns {
        named_in(p, &mut named);
    }
    for (range, node) in named {
        consider(range, node);
    }
    best.map(|(_, node)| node)
}

/// The patterns that an expression holds directly: a closure's parameters, the arms of a
/// `match` or a `catch`, and the pattern of a `for` loop or an `if let`.
fn patterns_of(e: &Expr) -> Vec<&Pat> {
    match &e.kind {
        ExprKind::Closure(params, _) => params.iter().collect(),
        ExprKind::Match(_, arms) => arms.iter().map(|a| &a.pattern).collect(),
        ExprKind::Try(_, catch) => crate::tast::walk::catch_arms(catch.as_ref())
            .iter()
            .map(|a| &a.pattern)
            .collect(),
        ExprKind::For(p, ..) | ExprKind::IfLet(p, ..) => vec![p],
        _ => Vec::new(),
    }
}

/// The variables that `p` binds, each with the span of its binding and its type, and the
/// variants it names, each with the span of its pattern.
fn named_in<'a>(p: &'a Pat, out: &mut Vec<(TextRange, Node<'a>)>) {
    match &p.kind {
        PatKind::Bind(v) => out.push((p.at, Node::Bind(*v, &p.ty))),
        PatKind::Variant(_, ps) => {
            out.push((p.at, Node::Variant(&p.ty)));
            for q in ps {
                named_in(q, out);
            }
        }
        PatKind::Tuple(ps) | PatKind::Or(ps) | PatKind::List(ps, _) => {
            for q in ps {
                named_in(q, out);
            }
        }
        PatKind::Record(fields) => {
            for (_, q) in fields {
                named_in(q, out);
            }
        }
        PatKind::Wild
        | PatKind::Int(_)
        | PatKind::Str(_)
        | PatKind::Bool(_)
        | PatKind::Const(_)
        | PatKind::Error => {}
    }
}
