//! Whether a function fits a hole (goal hole-context): called on its receiver, if it has one,
//! its result can be the type the hole expects, and the hole may perform its effects.

use stilt_hir::decls::Lookup;
use stilt_syntax::TextRange;

use super::candidates::Candidate;
use super::{Allowed, Fit, Raise};
use crate::analyses::implicit::{Effect, Effects};
use crate::implements::{Bounds, implements_trait};
use crate::ty::{Kind, Row, Subst, Table, Ty};

/// The most functions that a hole's context lists.
pub const MOST: usize = 10;

/// What deciding a fit needs beside the candidate.
pub(super) struct Judge<'a> {
    pub(super) decls: &'a dyn Lookup,
    pub(super) bounds: &'a Bounds,
    pub(super) effects: &'a Effects,
}

impl Judge<'_> {
    /// The first [`MOST`] candidates that fit, each once.
    pub(super) fn select(
        &self,
        candidates: &[Candidate<'_>],
        expected: &Ty,
        allowed: &Allowed,
    ) -> Vec<Fit> {
        let mut found: Vec<Fit> = Vec::new();
        for c in candidates {
            if found.len() == MOST {
                break;
            }
            if !found.contains(&c.fit) && self.fits(c, expected, allowed) {
                found.push(c.fit.clone());
            }
        }
        found
    }

    /// Whether `c` fits. A result that is one of the candidate's own type parameters, which
    /// nothing in the call fixes, would fit every hole and tell nothing, so it doesn't fit.
    fn fits(&self, c: &Candidate<'_>, expected: &Ty, allowed: &Allowed) -> bool {
        let mut table = Table::default();
        let mut s = Subst {
            self_ty: c.receiver.clone(),
            ..Subst::default()
        };
        for (g, _) in &c.sig.type_params {
            let v = table.fresh(Kind::Any, TextRange::default());
            s.types.push((g.clone(), v));
        }
        if let Some(t) = c.self_ty {
            s.self_ty = Some(table.subst(&s, &Ty::from_hir(t, None)));
        }
        if let Some(receiver) = &c.receiver {
            let Some((_, first)) = c.sig.params.first() else {
                return false;
            };
            let first = table.subst(&s, &Ty::from_hir(first, s.self_ty.as_ref()));
            if !table.unify(&first, receiver) {
                return false;
            }
        }
        let ret = table.subst(&s, &Ty::from_hir(&c.sig.ret, s.self_ty.as_ref()));
        if table.mentions_error(&ret) || matches!(table.resolve(&ret), Ty::Var(_)) {
            return false;
        }
        let row = table.subst_row(&s, &Row::from_hir(&c.sig.row, s.self_ty.as_ref()));
        table.unify(&ret, expected)
            && self.bounded(&table, c, &s)
            && self.allows(&mut table, &row, allowed)
            && self.within_limits(c, allowed)
    }

    /// Whether each type parameter of the candidate that the call fixes implements the traits
    /// that bound it. One that holds a type the call doesn't fix may yet, and counts as one
    /// that does.
    fn bounded(&self, table: &Table, c: &Candidate<'_>, s: &Subst) -> bool {
        c.sig
            .type_params
            .iter()
            .zip(&s.types)
            .all(|((_, traits), (_, v))| {
                let t = table.freeze(v);
                unfixed(&t)
                    || traits
                        .iter()
                        .all(|tr| implements_trait(self.decls, (self.bounds, &[]), &t, tr))
            })
    }

    /// Whether code at the hole may perform the labels of `row`: `io` only where the hole's
    /// row holds it, and a raise only of the error type the hole may raise.
    fn allows(&self, table: &mut Table, row: &Row, allowed: &Allowed) -> bool {
        if row.io && !allowed.io {
            return false;
        }
        match (&row.raise, &allowed.raise) {
            (None, _) => true,
            (Some(_), Raise::Nothing) => false,
            (Some(t), Raise::Of(e)) => table.unify(t, e),
            (Some(t), Raise::Showable) => {
                let t = table.freeze(t);
                implements_trait(self.decls, (self.bounds, &[]), &t, &show())
            }
        }
    }

    /// Whether the candidate's implicit effects are within the limits of the hole's function
    /// (facts.without; effects.without-panic; facts.without-div; facts.without). One whose effects
    /// aren't known is,
    /// and so is one that copies shared data, which only the modes of `stilt-rc` know.
    fn within_limits(&self, c: &Candidate<'_>, allowed: &Allowed) -> bool {
        let Some(key) = &c.key else {
            return true;
        };
        let rules_out = |limited: bool, effect| limited && self.effects.has(effect, key);
        !rules_out(allowed.limits.panic, Effect::Panic)
            && !rules_out(allowed.limits.alloc, Effect::Alloc)
            && !rules_out(allowed.limits.div, Effect::Div)
            && !allowed
                .limits
                .capabilities
                .iter()
                .any(|capability| self.effects.has(Effect::Capability(capability), key))
    }
}

/// Whether a type holds a type variable.
fn unfixed(t: &Ty) -> bool {
    match t {
        Ty::Var(_) => true,
        Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().any(unfixed),
        Ty::Fn(f) => unfixed(&f.ret) || f.params.iter().any(|(_, t)| unfixed(t)),
        Ty::Spread(s) => unfixed(&s.pack) || unfixed(&s.elem),
        Ty::Param(_) | Ty::Handler(_) | Ty::SelfTy | Ty::App(..) | Ty::Value(_) | Ty::Error => {
            false
        }
    }
}

/// The prelude's `Show`, which a test's errors implement (program.test-results).
fn show() -> stilt_hir::hir::Item {
    stilt_hir::decls::prelude_item("Show")
}
