//! Polymorphic function types (polymorphism.function-types and polymorphism.instantiation): their
//! type parameters, the bounds of each, sorted, and the arguments the bounds give traits with
//! parameters (traits.bound-arguments).

use stilt_hir::hir::{self, GenericId, Item};

use super::{FnTy, Ty};

impl FnTy {
    /// Whether it is a polymorphic function type (polymorphism.function-types).
    #[must_use]
    pub fn is_poly(&self) -> bool {
        !self.generics.is_empty()
    }

    /// The arguments its bounds give traits with parameters, each replaced by `f`'s.
    #[must_use]
    pub fn bound_args_with(&self, f: impl Fn(&Ty) -> Ty) -> Vec<(GenericId, Item, Vec<Ty>)> {
        self.bound_args
            .iter()
            .map(|(g, t, args)| (g.clone(), t.clone(), args.iter().map(&f).collect()))
            .collect()
    }

    /// The function type without its type parameters, which its parameters and result then
    /// name as rigid types.
    #[must_use]
    pub fn body(&self) -> Self {
        Self {
            generics: Vec::new(),
            bound_args: Vec::new(),
            ..self.clone()
        }
    }
}

/// The traits that bound a type parameter of a polymorphic function type, sorted, so that two such
/// types that list them in another order are the same (polymorphism.instantiation). A bound with an
/// error is left out, since the error type satisfies every bound (errors.error-type).
pub(super) fn poly_bounds(bounds: &[hir::TraitRef]) -> Vec<Item> {
    let mut traits: Vec<Item> = bounds
        .iter()
        .filter_map(|b| match b {
            hir::TraitRef::Trait(item, _) => Some(item.clone()),
            hir::TraitRef::Error => None,
        })
        .collect();
    traits.sort();
    traits.dedup();
    traits
}

/// The arguments that the bounds of a polymorphic function type's parameters give traits with
/// parameters, by parameter and then by trait, so that two such types that list the bounds in
/// another order are the same (polymorphism.instantiation; traits.bound-arguments).
pub(super) fn poly_bound_args(
    f: &hir::FnTy,
    self_ty: Option<&Ty>,
) -> Vec<(GenericId, Item, Vec<Ty>)> {
    let mut out = Vec::new();
    for (g, bounds) in &f.generics {
        let mut own: Vec<(GenericId, Item, Vec<Ty>)> = bounds
            .iter()
            .filter_map(|b| match b {
                hir::TraitRef::Trait(item, args) if !args.is_empty() => Some((
                    g.clone(),
                    item.clone(),
                    args.iter().map(|a| Ty::from_hir(a, self_ty)).collect(),
                )),
                _ => None,
            })
            .collect();
        own.sort_by(|a, b| a.1.cmp(&b.1));
        out.extend(own);
    }
    out
}

impl Ty {
    /// Whether the type is a polymorphic function type (polymorphism.function-types).
    #[must_use]
    pub fn is_poly(&self) -> bool {
        matches!(self, Self::Fn(f) if f.is_poly())
    }
}
