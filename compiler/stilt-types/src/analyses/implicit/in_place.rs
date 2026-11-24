//! In-place parameters (facts.in-place-parameters): the parameters of functions limited by `without
//! alloc` whose storage reaches a write in place, solved as a fixed point over the call graph,
//! from no parameter in place.

use std::collections::BTreeMap;

use stilt_hir::decls::Lookup;
use stilt_hir::hir::{LocalId, Mode, Name};
use stilt_syntax::TextRange;

use super::storage::{Origin, Storage};
use super::{Key, Scope, walk_code};
use crate::Cow;
use crate::tast::{Arg, Callee, Definition, Expr, ExprKind, StmtKind};
use crate::ty::Ty;

/// The in-place parameters of each function that has one, by their places, a receiver first.
pub type InPlace = BTreeMap<Key, Vec<usize>>;

/// What the fixed point needs of the body of a function limited by `without alloc`: each
/// parameter whose storage it writes in place, and each place where it passes a parameter's
/// storage on, named whole, to a parameter of a callee, each with where it is.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Summary {
    pub(crate) direct: Vec<(usize, TextRange)>,
    /// The parameter, the callee and its parameter, and where.
    pub(crate) passes: Vec<(usize, Key, usize, TextRange)>,
}

/// The item that a call names, for the rule: a function, a method, or a trait method whose
/// impl is known (facts.inference).
pub fn called(decls: &dyn Lookup, c: &Callee) -> Option<Key> {
    match c {
        Callee::Function(item) => Some(Key::Function(item.clone())),
        Callee::Member(owner, name) => Some(Key::Member(owner.clone(), *name)),
        Callee::TraitMethod(t, name, Ty::Con(owner, _)) => {
            let imp = decls.trait_impl(t, owner)?;
            if imp.members.iter().any(|m| m.name == *name) {
                Some(Key::ImplMethod(t.clone(), owner.clone(), *name))
            } else {
                Some(Key::DefaultMethod(t.clone(), *name))
            }
        }
        // An operation runs the nearest handler's body, which no key names
        // (handlers.performing-operation).
        Callee::TraitMethod(..) | Callee::Operation(..) => None,
    }
}

/// Whether a call is `view.into` or `view.split`, which write their `inout` list in place when it
/// holds its own storage (facts.writes-in-place; projections.writable-views and
/// projections.writable-bindings).
pub(super) fn is_window(c: &Callee) -> bool {
    matches!(c, Callee::Function(item)
        if &*item.home == "std.view" && matches!(&*item.name, "into" | "split"))
}

/// The binding of the list that an assignment to `place` writes an element of
/// (facts.writes-in-place): `b[i]` for a list `b`, or a place that goes on from `b[i]` through
/// fields, tuple elements and elements of arrays when `b`'s elements aren't of a copy-on-write type
/// (modes.copy-on-write-types), so that nothing an element holds is shared with another.
pub(super) fn written_list(decls: &dyn Lookup, place: &Expr) -> Option<LocalId> {
    let mut at = place;
    let mut inside = false;
    loop {
        match &at.kind {
            ExprKind::Index(base, _) if base.ty.arrayed().is_some() => at = base,
            ExprKind::Field(base, _) | ExprKind::TupleField(base, _) => at = base,
            ExprKind::Index(base, _) => {
                let ExprKind::Local(v) = base.kind else {
                    return None;
                };
                let Ty::Con(_, args) = &base.ty else {
                    return None;
                };
                let plain = || args.first().is_some_and(|t| !Cow::new(decls).ty(t));
                return (base.ty.is_prelude("List") && (!inside || plain())).then_some(v);
            }
            _ => return None,
        }
        inside = true;
    }
}

/// Whether `a` names a binding whole, as a `List`.
pub(super) fn named_list(a: &Arg) -> Option<stilt_hir::hir::LocalId> {
    match a.value.kind {
        ExprKind::Local(v) if a.value.ty.is_prelude("List") => Some(v),
        _ => None,
    }
}

/// Whether passing `a` to an in-place parameter needs no copy (facts.copy-at-call), and where the
/// storage it names comes from: it names whole a binding that holds its own storage, at its
/// last use for a `let` parameter.
pub(super) fn handed(storage: &Storage<'_>, a: &Arg) -> Option<Vec<Origin>> {
    let v = named_list(a)?;
    let at = a.value.at.start();
    if a.mode == Mode::Let && !storage.last_use(v, at) {
        return None;
    }
    storage.own(v, at)
}

/// The places among the body's parameters of the parameters whose storage `origins` are.
fn params(scope: &Scope<'_>, origins: Vec<Origin>) -> Vec<usize> {
    let position = |v| scope.body.params.iter().position(|(_, p)| *p == v);
    let mut found: Vec<usize> = origins
        .into_iter()
        .filter_map(|o| match o {
            Origin::Param(v) => position(v),
            Origin::Fresh => None,
        })
        .collect();
    found.sort_unstable();
    found.dedup();
    found
}

/// The summary of a body, which `scope` limits by `without alloc`.
pub(crate) fn summary(decls: &dyn Lookup, scope: &Scope<'_>) -> Summary {
    let Definition::Code(code) = &scope.body.code else {
        return Summary::default();
    };
    if !scope.limits.alloc {
        return Summary::default();
    }
    let found = std::cell::RefCell::new(Summary::default());
    let storage = Storage::of(scope.body, code, true);
    let written = |v, at| storage.own(v, at).map_or(Vec::new(), |o| params(scope, o));
    let handed_on = |a| handed(&storage, a).map_or(Vec::new(), |o| params(scope, o));
    walk_code(
        code,
        &mut |s| {
            if let StmtKind::Assign(_, place, _) = &s.kind
                && let Some(v) = written_list(decls, place)
            {
                for p in written(v, s.at.start()) {
                    found.borrow_mut().direct.push((p, place.at));
                }
            }
        },
        &mut |e| {
            let ExprKind::Call(c, _, args, _) = &e.kind else {
                return;
            };
            if is_window(c) {
                for p in args.first().map_or(Vec::new(), handed_on) {
                    found.borrow_mut().direct.push((p, e.at));
                }
                return;
            }
            let Some(callee) = called(decls, c) else {
                return;
            };
            for (i, a) in args.iter().enumerate() {
                for p in handed_on(a) {
                    found
                        .borrow_mut()
                        .passes
                        .push((p, callee.clone(), i, a.value.at));
                }
            }
        },
    );
    found.into_inner()
}

/// facts.in-place-parameters: the in-place parameters of the program, as a least fixed point over
/// each limited function's summary.
pub(crate) fn solve(summaries: &[(Key, Summary)]) -> InPlace {
    let mut in_place: BTreeMap<Key, Vec<usize>> = BTreeMap::new();
    loop {
        let mut changed = false;
        for (key, s) in summaries {
            let reaches = |p: usize| {
                s.direct.iter().any(|(q, _)| *q == p)
                    || s.passes.iter().any(|(q, callee, i, _)| {
                        *q == p && in_place.get(callee).is_some_and(|ps| ps.contains(i))
                    })
            };
            let params: Vec<usize> = s
                .direct
                .iter()
                .map(|(p, _)| *p)
                .chain(s.passes.iter().map(|(p, ..)| *p))
                .filter(|p| reaches(*p))
                .collect();
            let entry = in_place.entry(key.clone()).or_default();
            for p in params {
                if !entry.contains(&p) {
                    entry.push(p);
                    changed = true;
                }
            }
        }
        if !changed {
            in_place.retain(|_, ps| {
                ps.sort_unstable();
                !ps.is_empty()
            });
            return in_place;
        }
    }
}

/// The lines that make each in-place parameter of a function in place (facts.facts-suite): its
/// writes in place, and the places where it passes the parameter on to an in-place parameter,
/// each with the parameter's name.
pub(crate) fn causes(
    summary: &Summary,
    key: &Key,
    in_place: &InPlace,
    names: &[Name],
) -> Vec<(Name, TextRange)> {
    let Some(params) = in_place.get(key) else {
        return Vec::new();
    };
    let mut found: Vec<(usize, TextRange)> = summary
        .direct
        .iter()
        .copied()
        .chain(summary.passes.iter().filter_map(|(p, callee, i, at)| {
            in_place
                .get(callee)
                .is_some_and(|ps| ps.contains(i))
                .then_some((*p, *at))
        }))
        .filter(|(p, _)| params.contains(p))
        .collect();
    found.sort_by_key(|(_, at)| at.start());
    found
        .into_iter()
        .filter_map(|(p, at)| Some((*names.get(p)?, at)))
        .collect()
}
