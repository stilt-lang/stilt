//! Names that a pattern writes without a module, which name the variant of the type matched
//! before any other meaning, and otherwise what they name in scope (patterns.variants-by-type).

use std::collections::HashSet;

use stilt_diag::{AlternativeKind, Diagnostic, codes};
use stilt_hir::decls::TypeDefInfo;
use stilt_hir::hir::{self, Failure, Fallback, Ident, Item, Name, PatKind};

use super::refutable::Named;
use super::{Cx, State};
use crate::tast;
use crate::ty::Ty;

/// A failure as resolution found it, where the type matched is unknown, with the names in scope
/// close to the name as its candidates.
fn in_scope(n: &Ident, failure: &Failure) -> Diagnostic {
    let close = failure.close.iter().map(|c| &**c);
    Diagnostic::new(failure.code, n.at, failure.message.clone()).with_closest(
        AlternativeKind::Name,
        n.at,
        &n.name,
        close,
    )
}

impl State<'_> {
    pub(super) fn bare_pattern(
        &mut self,
        cx: &mut Cx,
        p: &hir::Pat,
        ty: &Ty,
        (n, ps, fallback): (&Ident, &[hir::Pat], &Fallback),
    ) -> tast::PatKind {
        // meta.shapes: the cases of a shape, which patterns name as a variant
        // type's.
        if let Some(case) = self.shape_case(cx, p, ty, (n, ps)) {
            self.bare
                .insert(p.at, Named::Variant(crate::ty::meta_item(&n.name)));
            return case;
        }
        let variant = self
            .matched_variant(ty, &n.name)
            .or_else(|| match fallback {
                Fallback::Variant(item) => Some(item.clone()),
                _ => None,
            });
        if let Some(item) = variant {
            self.bare.insert(p.at, Named::Variant(item.clone()));
            return self.variant_pattern(cx, p, ty, &item, ps);
        }
        if let Fallback::Const(item) = fallback {
            self.bare.insert(p.at, Named::Const);
            return self.const_pattern(p, ty, item);
        }
        self.bare.insert(p.at, Named::Error);
        if let Fallback::Failed(failure) = fallback {
            self.failed(ty, n, failure);
        }
        self.broken = true;
        for q in ps {
            self.unchecked(q);
        }
        tast::PatKind::Error
    }

    /// The names of the variants of `owner`, if it is a variant type.
    fn variant_names(&self, owner: &Item) -> Option<Vec<Name>> {
        match &self.env.decls.type_info(owner)?.def {
            TypeDefInfo::Variants(vs) => Some(vs.iter().map(|(n, _)| *n).collect()),
            TypeDefInfo::Record(_) | TypeDefInfo::Builtin => None,
        }
    }

    /// The error of a name that names no variant or constant, matched against `ty`. A type
    /// with variants is named in an E0211, and the variants close to the name are its fixes
    /// and alternatives, since they are the names it could have meant (goal closest-candidates and
    /// admissible-alternatives).
    fn failed(&mut self, ty: &Ty, n: &Ident, failure: &Failure) {
        let resolved = self.resolved(ty);
        let variants = match &resolved {
            Ty::Con(owner, _) if failure.code == codes::E0211 => self.variant_names(owner),
            _ => None,
        };
        let d = match variants {
            Some(names) => {
                let message = format!("`{}` has no variant `{}`", self.show(&resolved), n.name);
                let names = names.iter().map(|v| &**v);
                Diagnostic::new(codes::E0211, n.at, message).with_closest(
                    AlternativeKind::Name,
                    n.at,
                    &n.name,
                    names,
                )
            }
            None => in_scope(n, failure),
        };
        self.report_failure(n, d);
    }

    /// The error of a name without a module, of which the body keeps one E0211 per name
    /// (errors.unknown-names).
    fn report_failure(&mut self, n: &Ident, d: Diagnostic) {
        if d.code == codes::E0211 {
            self.unknown_names.push((n.name, self.errors.len()));
        }
        self.errors.push(d);
    }

    /// The parts of a pattern with an error, which aren't checked: their types are unknown, so
    /// each name in them written without a module means what it means in scope, and an error
    /// there is reported.
    fn unchecked(&mut self, p: &hir::Pat) {
        match &p.kind {
            PatKind::Bare(n, ps, fallback) => {
                if let Fallback::Failed(failure) = &**fallback {
                    self.report_failure(n, in_scope(n, failure));
                }
                for q in ps {
                    self.unchecked(q);
                }
            }
            PatKind::Tuple(ps)
            | PatKind::Variant(_, ps)
            | PatKind::List(ps, _)
            | PatKind::Or(ps) => {
                for q in ps {
                    self.unchecked(q);
                }
            }
            PatKind::Record(_, fields, _) | PatKind::AnonRecord(fields, _) => {
                for f in fields {
                    self.unchecked(&f.pattern);
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

    /// errors.unknown-names: the body keeps one E0211 for each name that doesn't resolve in it,
    /// where that name starts first, among those of the names that its patterns write without a
    /// module and those that resolution `held` back for the same names.
    pub(super) fn settle_unknown_names(&mut self, held: &[(Name, Diagnostic)]) {
        let found = std::mem::take(&mut self.unknown_names);
        let earliest = |name: &Name, errors: &[Diagnostic]| {
            let checked = found.iter().filter(|(n, _)| n == name);
            let resolved = held.iter().filter(|(n, _)| n == name);
            checked
                .map(|&(_, i)| errors[i].range.start())
                .chain(resolved.map(|(_, d)| d.range.start()))
                .min()
        };
        let dropped: HashSet<usize> = found
            .iter()
            .filter(|(n, i)| earliest(n, &self.errors) != Some(self.errors[*i].range.start()))
            .map(|&(_, i)| i)
            .collect();
        let kept: Vec<Diagnostic> = held
            .iter()
            .filter(|(n, d)| earliest(n, &self.errors) == Some(d.range.start()))
            .map(|(_, d)| d.clone())
            .collect();
        let mut index = 0;
        self.errors.retain(|_| {
            index += 1;
            !dropped.contains(&(index - 1))
        });
        self.errors.extend(kept);
    }
}
