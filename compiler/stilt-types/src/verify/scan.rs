//! What the analysis reads of a body's text before following its values: the kind of each binding,
//! the count of facts.large-bodies, each loop's thresholds and the bindings it changes
//! (facts.loop-heads), and each closure literal's captures (facts.terms).

use std::collections::{BTreeSet, HashMap};

use stilt_hir::decls::Lookup;
use stilt_hir::hir::{Item, ListRest, LocalId, Mode, Value as Constant};

use super::Context;
use super::values::type_bounds;
use crate::tast::walk::{Part, iter, iter_block, parts, stmt_exprs};
use crate::tast::{Code, Expr, ExprKind, Iterable, Pat, PatKind, Stmt, StmtKind, TypedBody};
use crate::ty::{INTEGER_TYPES, Ty, is_prelude};

/// What a binding's value is to the analysis.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    /// An integer, within these bounds.
    Int(i128, i128),
    List,
    /// A map, and whether its keys can be found again once found (facts.map-keys).
    Map(bool),
    Other,
    /// A name of a `when`, which has no term, length or version (facts.terms).
    Unbound,
}

/// The kinds of a body's bindings, its closures' included.
pub(crate) struct Info {
    kinds: HashMap<LocalId, Kind>,
}

impl Info {
    pub(crate) fn of(cx: &Context<'_>, body: &TypedBody, code: &Code) -> Self {
        let mut kinds = HashMap::new();
        for ((_, v), ty) in body.params.iter().zip(&cx.params) {
            kinds.insert(*v, kind_of(cx.decls, ty));
        }
        let (mut named, mut declared, mut unbound) = (Vec::new(), Vec::new(), Vec::new());
        let mut expr = |e: &Expr| match &e.kind {
            ExprKind::Local(v) => named.push((*v, e.ty.clone())),
            ExprKind::When(held, _) => unbound.extend(held.iter().map(|(_, v)| *v)),
            ExprKind::Closure(params, _) => {
                for p in params {
                    patterns(p, &mut |v, ty| named.push((v, ty.clone())));
                }
            }
            _ => bound_in(e, &mut |v, ty| named.push((v, ty.clone()))),
        };
        let mut stmt = |s: &Stmt| {
            if let StmtKind::Let(b) | StmtKind::Var(b) = &s.kind {
                patterns(&b.pattern, &mut |v, ty| declared.push((v, ty.clone())));
            }
        };
        match code {
            Code::Block(b) => iter_block(b, &mut stmt, &mut expr),
            Code::Expr(e) => iter(e, &mut stmt, &mut expr),
        }
        // A binding's pattern gives its type, and otherwise a use of it does.
        for (v, ty) in named {
            kinds.entry(v).or_insert_with(|| kind_of(cx.decls, &ty));
        }
        for (v, ty) in declared {
            kinds.insert(v, kind_of(cx.decls, &ty));
        }
        for v in unbound {
            kinds.insert(v, Kind::Unbound);
        }
        Self { kinds }
    }

    pub(crate) fn kind(&self, v: LocalId) -> Kind {
        self.kinds.get(&v).copied().unwrap_or(Kind::Other)
    }
}

/// The bindings that the patterns of an expression's arms, `for` and `if let` bind.
fn bound_in(e: &Expr, f: &mut dyn FnMut(LocalId, &Ty)) {
    match &e.kind {
        ExprKind::Match(_, arms) => arms.iter().for_each(|a| patterns(&a.pattern, f)),
        ExprKind::Try(_, Some(c)) => c.arms.iter().for_each(|a| patterns(&a.pattern, f)),
        ExprKind::IfLet(p, ..) | ExprKind::For(p, ..) => patterns(p, f),
        _ => {}
    }
}

/// Each binding a pattern binds, with its type.
pub(crate) fn patterns(p: &Pat, f: &mut dyn FnMut(LocalId, &Ty)) {
    match &p.kind {
        PatKind::Bind(v) => f(*v, &p.ty),
        PatKind::Tuple(ps) | PatKind::Variant(_, ps) | PatKind::Or(ps) => {
            for p in ps {
                patterns(p, f);
            }
        }
        PatKind::Record(fields) => fields.iter().for_each(|(_, p)| patterns(p, f)),
        PatKind::List(ps, rest) => {
            for p in ps {
                patterns(p, f);
            }
            if let ListRest::Bind(v) = rest {
                f(*v, &p.ty);
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

/// What a binding of type `ty` is.
pub(crate) fn kind_of(decls: &dyn Lookup, ty: &Ty) -> Kind {
    if let Some((lo, hi)) = ty.integer_name().and_then(type_bounds) {
        return Kind::Int(lo, hi);
    }
    match ty {
        Ty::Con(item, _) if is_prelude(item, "List") => Kind::List,
        Ty::Con(item, args) if is_prelude(item, "Map") => Kind::Map(
            args.first()
                .is_some_and(|k| keyable(decls, k, &mut Vec::new())),
        ),
        _ => Kind::Other,
    }
}

/// Whether the `Eq` and `Hash` of a key type are a primitive type's, a float's apart, whose NaN
/// isn't found again, or structural throughout its parts, never a type parameter's
/// (facts.map-keys).
pub(crate) fn keyable(decls: &dyn Lookup, ty: &Ty, visiting: &mut Vec<Item>) -> bool {
    match ty {
        Ty::Con(item, args) => {
            if &*item.home == "std.prelude" && matches!(&*item.name, "f32" | "f64") {
                return false;
            }
            if &*item.home == "std.prelude" && is_primitive(&item.name) {
                return true;
            }
            let written = ["Eq", "Hash"].iter().any(|t| {
                decls
                    .trait_impl(&stilt_hir::decls::prelude_item(t), item)
                    .is_some()
            });
            if written {
                return false;
            }
            if visiting.contains(item) {
                return true;
            }
            visiting.push(item.clone());
            let parts = crate::analyses::implicit::held(decls, item, args);
            let all = parts.iter().all(|p| keyable(decls, p, visiting));
            visiting.pop();
            all
        }
        Ty::Tuple(ts) => ts.iter().all(|t| keyable(decls, t, visiting)),
        _ => false,
    }
}

fn is_primitive(name: &str) -> bool {
    INTEGER_TYPES.contains(&name) || matches!(name, "bool" | "str" | "char" | "()")
}

/// The count of facts.large-bodies for a code: its own bindings of integers and lists outside its
/// closures and handlers, `own` holding its parameters and captures, three for each `for` over a
/// range, whose variable they count, the value parameters, and zero.
pub(crate) fn count(info: &Info, own: &[LocalId], code: &[Part<'_>], values: usize) -> usize {
    let counted = |v: &LocalId| matches!(info.kind(*v), Kind::Int(..) | Kind::List);
    let mut n = own.iter().filter(|v| counted(v)).count();
    let (mut bound, mut skipped) = (BTreeSet::new(), BTreeSet::new());
    let mut ranges = 0;
    let mut expr = |e: &Expr| {
        if let ExprKind::For(p, iterable, _) = &e.kind
            && let Iterable::Range(..) = **iterable
        {
            ranges += 3;
            if let PatKind::Bind(v) = p.kind {
                skipped.insert(v);
            }
        }
        bound_in(e, &mut |v, _| {
            bound.insert(v);
        });
    };
    let mut lets = BTreeSet::new();
    let mut stmt = |s: &Stmt| {
        if let StmtKind::Let(b) | StmtKind::Var(b) = &s.kind {
            patterns(&b.pattern, &mut |v, _| {
                lets.insert(v);
            });
        }
    };
    walk_own(code, &mut stmt, &mut expr);
    bound.extend(lets);
    n += bound
        .iter()
        .filter(|v| counted(v) && !skipped.contains(v))
        .count();
    n + ranges + values + 1
}

/// Applies `stmt` and `expr` to the statements and expressions of `code`, in the order written,
/// but those of its closure and handler literals.
pub(crate) fn walk_own<'e>(
    code: &[Part<'e>],
    stmt: &mut dyn FnMut(&'e Stmt),
    expr: &mut dyn FnMut(&'e Expr),
) {
    for part in code {
        match part {
            Part::Expr(e) => own_expr(e, stmt, expr),
            Part::Block(b) => own_block(b, stmt, expr),
        }
    }
}

fn own_expr<'e>(e: &'e Expr, stmt: &mut dyn FnMut(&'e Stmt), expr: &mut dyn FnMut(&'e Expr)) {
    expr(e);
    if matches!(e.kind, ExprKind::Closure(..) | ExprKind::Handler(_)) {
        return;
    }
    walk_own(&parts(e), stmt, expr);
}

fn own_block<'e>(b: &'e [Stmt], stmt: &mut dyn FnMut(&'e Stmt), expr: &mut dyn FnMut(&'e Expr)) {
    for s in b {
        stmt(s);
        for e in stmt_exprs(s) {
            own_expr(e, stmt, expr);
        }
    }
}

/// The binding a place is rooted in, if it is rooted in one.
pub(crate) fn root(place: &Expr) -> Option<LocalId> {
    match &place.kind {
        ExprKind::Local(v) => Some(*v),
        ExprKind::Field(b, _) | ExprKind::TupleField(b, _) | ExprKind::Index(b, _) => root(b),
        _ => None,
    }
}

/// The bindings that a loop's code may give a new term, length or version: those it assigns,
/// passes `inout`, yields or writes through a place, outside its closures and handlers, whose
/// bodies change none of the caller's (expressions.closure-boundaries).
pub(crate) fn modified(code: &[Part<'_>]) -> BTreeSet<LocalId> {
    let mut out = BTreeSet::new();
    let mut written = Vec::new();
    let mut stmt = |s: &Stmt| {
        if let StmtKind::Assign(_, place, _) | StmtKind::Yield(place) = &s.kind {
            written.extend(root(place));
            written.extend(project_roots(place));
        }
    };
    let mut expr = |e: &Expr| {
        if let ExprKind::Call(_, _, a, _)
        | ExprKind::Project(_, _, a, _)
        | ExprKind::CallValue(_, a) = &e.kind
        {
            out.extend(
                a.iter()
                    .filter(|a| a.mode == Mode::Inout)
                    .flat_map(|a| root(&a.value).into_iter().chain(project_roots(&a.value))),
            );
        }
    };
    walk_own(code, &mut stmt, &mut expr);
    out.extend(written);
    out
}

/// The bindings that the `inout` arguments of a projection's call that roots a place write.
fn project_roots(place: &Expr) -> Vec<LocalId> {
    match &place.kind {
        ExprKind::Project(_, _, args, _) => args
            .iter()
            .filter(|a| a.mode == Mode::Inout)
            .filter_map(|a| root(&a.value))
            .collect(),
        ExprKind::Field(b, _) | ExprKind::TupleField(b, _) | ExprKind::Index(b, _) => {
            project_roots(b)
        }
        _ => Vec::new(),
    }
}

/// The numbers of a code (facts.widening): its integer-typed literals, its closures, patterns and
/// value arguments included, and the values of the constants of facts.terms it names, each with its
/// negation.
pub(crate) fn numbers(cx: &Context<'_>, code: &[Part<'_>], pats: &[&Pat]) -> BTreeSet<i128> {
    let mut found = BTreeSet::new();
    let mut expr = |e: &Expr| literals(cx, e, &mut found);
    for part in code {
        match part {
            Part::Expr(e) => iter(e, &mut |_| {}, &mut expr),
            Part::Block(b) => iter_block(b, &mut |_| {}, &mut expr),
        }
    }
    for p in pats {
        pattern_literals(p, &mut found);
    }
    found.iter().flat_map(|n| [*n, -n]).collect()
}

/// A loop's thresholds (facts.widening): the numbers of its text, each with those plus one and
/// minus one; the bounds of the eight integer types; 0 and 2^48. In increasing order.
pub(crate) fn thresholds(cx: &Context<'_>, code: &[Part<'_>], pats: &[&Pat]) -> Vec<i128> {
    let mut out = BTreeSet::new();
    for m in numbers(cx, code, pats) {
        out.extend([m - 1, m, m + 1]);
    }
    for name in INTEGER_TYPES {
        if let Some((lo, hi)) = type_bounds(name) {
            out.extend([lo, hi]);
        }
    }
    out.extend([0, 1 << 48]);
    out.into_iter().collect()
}

fn literals(cx: &Context<'_>, e: &Expr, found: &mut BTreeSet<i128>) {
    match &e.kind {
        ExprKind::Int(text) if e.ty.integer_name().is_some() => {
            found.extend(literal(text));
        }
        ExprKind::Constant(item) => found.extend((cx.literal)(item, None)),
        ExprKind::MemberConstant(item, name, _) => found.extend((cx.literal)(item, Some(*name))),
        ExprKind::Match(_, arms) => arms
            .iter()
            .for_each(|a| pattern_literals(&a.pattern, found)),
        ExprKind::IfLet(p, ..) | ExprKind::For(p, ..) => pattern_literals(p, found),
        ExprKind::Closure(ps, _) => ps.iter().for_each(|p| pattern_literals(p, found)),
        _ => {}
    }
    let types: Vec<&Ty> = match &e.kind {
        ExprKind::Call(_, targs, ..)
        | ExprKind::Project(_, targs, ..)
        | ExprKind::Callee(_, targs)
        | ExprKind::Construct(_, targs, _)
        | ExprKind::Record(_, targs, _)
        | ExprKind::Constructor(_, targs)
        | ExprKind::MemberConstant(_, _, targs)
        | ExprKind::Instantiate(_, targs) => targs.iter().collect(),
        _ => Vec::new(),
    };
    for t in types {
        value_arguments(t, found);
    }
}

/// The integer value arguments a type holds (generics.constant-arguments).
fn value_arguments(t: &Ty, found: &mut BTreeSet<i128>) {
    match t {
        Ty::Value(Constant::Int(n)) => {
            found.insert(*n);
        }
        Ty::Con(_, args) | Ty::Tuple(args) => args.iter().for_each(|a| value_arguments(a, found)),
        _ => {}
    }
}

fn pattern_literals(p: &Pat, found: &mut BTreeSet<i128>) {
    match &p.kind {
        PatKind::Int(text) if p.ty.integer_name().is_some() => found.extend(literal(text)),
        PatKind::Tuple(ps) | PatKind::Variant(_, ps) | PatKind::Or(ps) | PatKind::List(ps, _) => {
            for p in ps {
                pattern_literals(p, found);
            }
        }
        PatKind::Record(fields) => fields.iter().for_each(|(_, p)| pattern_literals(p, found)),
        _ => {}
    }
}

/// The value of an integer literal's text, its `-` included.
pub(crate) fn literal(text: &str) -> Option<i128> {
    let text = text.replace('_', "");
    match text.strip_prefix('-') {
        Some(rest) => stilt_hir::values::int_literal(rest.trim(), true),
        None => stilt_hir::values::int_literal(&text, false),
    }
}

/// The bindings a closure literal's body names but doesn't bind: its captures (facts.terms).
pub(crate) fn captures(params: &[Pat], body: &Expr) -> Vec<LocalId> {
    let mut bound = BTreeSet::new();
    for p in params {
        patterns(p, &mut |v, _| {
            bound.insert(v);
        });
    }
    let mut named = BTreeSet::new();
    let mut lets = BTreeSet::new();
    iter(
        body,
        &mut |s| {
            if let StmtKind::Let(b) | StmtKind::Var(b) = &s.kind {
                patterns(&b.pattern, &mut |v, _| {
                    lets.insert(v);
                });
            }
        },
        &mut |e| {
            match &e.kind {
                ExprKind::Local(v) => {
                    named.insert(*v);
                }
                ExprKind::Closure(ps, _) => ps.iter().for_each(|p| {
                    patterns(p, &mut |v, _| {
                        bound.insert(v);
                    });
                }),
                ExprKind::When(held, _) => bound.extend(held.iter().map(|(_, v)| *v)),
                _ => {}
            }
            bound_in(e, &mut |v, _| {
                bound.insert(v);
            });
        },
    );
    bound.extend(lets);
    named.difference(&bound).copied().collect()
}
