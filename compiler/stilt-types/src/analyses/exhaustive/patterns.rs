//! The patterns of a typed body, as the algorithm reads them.

use stilt_hir::decls::Lookup;
use stilt_hir::hir::{ListRest, Name};

use super::ctors::{all_ctors, field_types, is_error, record_fields};
use super::{Ctor, Pat};
use crate::literal::int_canonical;
use crate::tast::{self, PatKind};
use crate::ty::Ty;

/// A pattern, with every constant read as `_` (patterns.guards-and-constants and
/// patterns.unreachable-arms).
pub(super) fn of_pattern(decls: &dyn Lookup, p: &tast::Pat) -> Pat {
    let all = |ps: &[tast::Pat]| -> Vec<Pat> { ps.iter().map(|p| of_pattern(decls, p)).collect() };
    match &p.kind {
        PatKind::Wild | PatKind::Bind(_) | PatKind::Const(_) | PatKind::Error => Pat::Wild,
        PatKind::Int(text) => Pat::Ctor(Ctor::Int(int_canonical(text)), Vec::new()),
        PatKind::Str(s) => Pat::Ctor(Ctor::Str(s.clone()), Vec::new()),
        PatKind::Bool(b) => Pat::Ctor(Ctor::Bool(*b), Vec::new()),
        PatKind::Tuple(ps) => Pat::Ctor(Ctor::Tuple(ps.len()), all(ps)),
        PatKind::Variant(item, ps) => Pat::Ctor(Ctor::Variant(item.clone()), all(ps)),
        PatKind::Record(given) => of_record(decls, &p.ty, given),
        PatKind::List(ps, _) if p.ty.arrayed().is_some() => of_array(&p.ty, all(ps)),
        PatKind::List(ps, ListRest::Exact) => Pat::Ctor(Ctor::Len(ps.len()), all(ps)),
        PatKind::List(ps, ListRest::Rest | ListRest::Bind(_)) => Pat::Prefix(all(ps)),
        PatKind::Or(ps) => of_or(decls, &p.ty, ps),
    }
}

/// A list pattern of an array of type `ty`, whose patterns are `ps`: an array of size `k` is
/// matched as a tuple of `k` elements, and `[p₁, …, pⱼ, ..]` as that tuple with `_` after its `j`
/// patterns (generics.array-patterns). Against a size that a value parameter gives, only `[..]`
/// fits.
fn of_array(ty: &Ty, mut ps: Vec<Pat>) -> Pat {
    match super::ctors::array_size(ty) {
        Some(k) => {
            ps.resize(k, Pat::Wild);
            Pat::Ctor(Ctor::Array(k), ps)
        }
        None => Pat::Wild,
    }
}

/// A record pattern of type `ty`, with `_` for each field it doesn't name.
fn of_record(decls: &dyn Lookup, ty: &Ty, given: &[(Name, tast::Pat)]) -> Pat {
    let Ty::Con(item, _) = ty else {
        return Pat::Wild;
    };
    let fields = record_fields(decls, item);
    let ps = fields
        .iter()
        .map(|f| {
            given
                .iter()
                .find(|(g, _)| g == f)
                .map_or(Pat::Wild, |(_, q)| of_pattern(decls, q))
        })
        .collect();
    Pat::Ctor(Ctor::Record(item.clone(), fields), ps)
}

/// An or-pattern of type `ty`, its nested alternatives flattened. One that lists every
/// constructor of its type, each with only wildcards inside, matches every value, so it is read
/// as `_` too, which keeps a tuple of such alternatives from splitting into every combination.
fn of_or(decls: &dyn Lookup, ty: &Ty, ps: &[tast::Pat]) -> Pat {
    let alts: Vec<Pat> = ps
        .iter()
        .flat_map(|q| match of_pattern(decls, q) {
            Pat::Or(qs) => qs,
            q => vec![q],
        })
        .collect();
    let bare = |c: &Ctor, q: &Pat| matches!(q, Pat::Ctor(d, qs) if d == c && qs.iter().all(|q| *q == Pat::Wild));
    let complete = match all_ctors(decls, ty) {
        Some(ctors) if !ctors.is_empty() => ctors.iter().all(|c| alts.iter().any(|q| bare(c, q))),
        _ => false,
    };
    if complete || alts.contains(&Pat::Wild) {
        Pat::Wild
    } else {
        Pat::Or(alts)
    }
}

/// Whether a pattern holds a constant, whose arm then leaves every value to later arms
/// (patterns.unreachable-arms).
pub(super) fn holds_constant(p: &tast::Pat) -> bool {
    match &p.kind {
        PatKind::Const(_) => true,
        PatKind::Tuple(ps) | PatKind::Variant(_, ps) | PatKind::List(ps, _) | PatKind::Or(ps) => {
            ps.iter().any(holds_constant)
        }
        PatKind::Record(fields) => fields.iter().any(|(_, q)| holds_constant(q)),
        PatKind::Wild
        | PatKind::Bind(_)
        | PatKind::Int(_)
        | PatKind::Str(_)
        | PatKind::Bool(_)
        | PatKind::Error => false,
    }
}

/// Whether a pattern, matched against a value of type `ty`, looks inside a part of the value
/// whose type has an error.
pub(super) fn touches_error(decls: &dyn Lookup, ty: &Ty, p: &Pat) -> bool {
    match p {
        Pat::Wild => false,
        _ if is_error(ty) => true,
        Pat::Or(ps) => ps.iter().any(|p| touches_error(decls, ty, p)),
        Pat::Ctor(c, ps) => inside(decls, &field_types(decls, ty, c), ps),
        Pat::Prefix(ps) => inside(decls, &field_types(decls, ty, &Ctor::AtLeast(ps.len())), ps),
    }
}

/// Whether the patterns of a constructor's fields, of types `tys`, look inside a part with an
/// error. Patterns that don't fit the fields can only come from one.
fn inside(decls: &dyn Lookup, tys: &[Ty], ps: &[Pat]) -> bool {
    tys.len() != ps.len() || tys.iter().zip(ps).any(|(t, p)| touches_error(decls, t, p))
}
