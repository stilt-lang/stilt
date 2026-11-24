//! Places (modes.places) as the modes read them: a binding with a path to a part of it, the
//! parts of a place that a pattern binds, and the bindings a closure literal captures.

use std::collections::HashSet;

use stilt_hir::hir::{ListRest, LocalId, Name};
use stilt_types::tast::walk;
use stilt_types::tast::{Expr, ExprKind, Pat, PatKind, StmtKind};
use stilt_types::ty::Ty;

/// A step from a place to a part of it. An index is kept only as a position.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Step {
    /// A field, or a tuple's element by its number written out.
    Field(Name),
    Index,
}

/// The binding a place is part of, and the path to the part, if the expression is a place.
pub(crate) fn place(e: &Expr) -> Option<(LocalId, Vec<Step>)> {
    let mut path = Vec::new();
    let mut e = e;
    loop {
        match &e.kind {
            ExprKind::Local(v) => {
                path.reverse();
                return Some((*v, path));
            }
            ExprKind::Field(base, name) => {
                path.push(Step::Field(*name));
                e = base;
            }
            ExprKind::TupleField(base, i) => {
                path.push(Step::Field(i.to_string().into()));
                e = base;
            }
            ExprKind::Index(base, _) => {
                path.push(Step::Index);
                e = base;
            }
            _ => return None,
        }
    }
}

/// The index expressions of a place, in order.
pub(crate) fn indexes(e: &Expr) -> Vec<&Expr> {
    let mut found = Vec::new();
    let mut e = e;
    loop {
        match &e.kind {
            ExprKind::Field(base, _) | ExprKind::TupleField(base, _) => e = base,
            ExprKind::Index(base, i) => {
                found.push(&**i);
                e = base;
            }
            _ => break,
        }
    }
    found.reverse();
    found
}

/// Whether two paths of a binding can reach a common part: whether, without their indexes, one
/// starts the other (modes.overlap).
pub(crate) fn overlap(a: &[Step], b: &[Step]) -> bool {
    let fields = |p: &[Step]| -> Vec<Name> {
        p.iter()
            .filter_map(|s| match s {
                Step::Field(f) => Some(*f),
                Step::Index => None,
            })
            .collect()
    };
    let (a, b) = (fields(a), fields(b));
    a.starts_with(&b) || b.starts_with(&a)
}

/// The parts of the place at `path` that a pattern binds, each with the variable that binds it
/// and its type. A variant's payload is a part of the variant that no place names apart.
pub(crate) fn pattern_parts(p: &Pat, path: &[Step], out: &mut Vec<(Vec<Step>, LocalId, Ty)>) {
    let with = |step: Step| -> Vec<Step> {
        let mut longer = path.to_vec();
        longer.push(step);
        longer
    };
    match &p.kind {
        PatKind::Bind(v) => out.push((path.to_vec(), *v, p.ty.clone())),
        PatKind::Record(fields) => {
            for (name, q) in fields {
                pattern_parts(q, &with(Step::Field(*name)), out);
            }
        }
        PatKind::Tuple(ps) => {
            for (i, q) in ps.iter().enumerate() {
                pattern_parts(q, &with(Step::Field(i.to_string().into())), out);
            }
        }
        PatKind::Variant(_, ps) | PatKind::Or(ps) => {
            for q in ps {
                pattern_parts(q, path, out);
            }
        }
        PatKind::List(ps, rest) => {
            for q in ps {
                pattern_parts(q, &with(Step::Index), out);
            }
            if let ListRest::Bind(v) = rest {
                out.push((with(Step::Index), *v, p.ty.clone()));
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

/// The variables a pattern binds.
pub(crate) fn binders(p: &Pat) -> Vec<LocalId> {
    let mut parts = Vec::new();
    pattern_parts(p, &[], &mut parts);
    parts.into_iter().map(|(_, v, _)| v).collect()
}

/// The bindings that a closure literal with these parameters and body captures, each once with
/// the type it has there, in the order the body first names them: those it names but doesn't
/// bind itself.
pub(crate) fn captures(params: &[Pat], body: &Expr) -> Vec<(LocalId, Ty)> {
    let mut bound: HashSet<LocalId> = params.iter().flat_map(binders).collect();
    let mut declared: Vec<LocalId> = Vec::new();
    let mut named: Vec<(LocalId, Ty)> = Vec::new();
    walk::iter(
        body,
        &mut |s| {
            if let StmtKind::Let(b) | StmtKind::Var(b) = &s.kind {
                declared.extend(binders(&b.pattern));
            }
        },
        &mut |e| match &e.kind {
            ExprKind::Local(v) if !named.iter().any(|(w, _)| w == v) => {
                named.push((*v, e.ty.clone()));
            }
            ExprKind::Closure(ps, _) => bound.extend(ps.iter().flat_map(binders)),
            ExprKind::IfLet(p, ..) | ExprKind::For(p, ..) => bound.extend(binders(p)),
            ExprKind::Match(_, arms) => bound.extend(arms.iter().flat_map(|a| binders(&a.pattern))),
            ExprKind::Try(_, Some(c)) => {
                bound.extend(c.arms.iter().flat_map(|a| binders(&a.pattern)));
            }
            ExprKind::When(held, _) => bound.extend(held.iter().map(|(_, place)| *place)),
            _ => {}
        },
    );
    bound.extend(declared);
    named.retain(|(v, _)| !bound.contains(v));
    named
}
