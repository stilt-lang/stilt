//! The arguments of traits with parameters (traits.trait-arguments, traits.bound-arguments and
//! traits.member-types): the ones an impl gives, instantiated for the type it is used at, and the
//! ones the bounds of the rigid types in scope give, through which member types are known.

use stilt_hir::decls::{ImplInfo, Lookup};
use stilt_hir::hir::{self, GenericId, Item};

use crate::ty::{Subst, Table, Ty};

/// The arguments that the bound of a rigid type in scope gives a trait with parameters: the
/// rigid type, its trait, and the arguments (traits.bound-arguments).
pub type BoundArg = (Ty, Item, Vec<Ty>);

/// Those of every bound in scope.
pub type BoundArgs = Vec<BoundArg>;

/// The arguments that a type gives a trait's parameters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TraitArgs {
    /// The arguments, one for each of the trait's parameters.
    Known(Vec<Ty>),
    /// The type is a variable not solved yet.
    Unknown,
    /// The type has no impl of the trait, and no bound of it.
    Missing,
}

/// Where the arguments of traits are looked up: the declarations, the arguments the bounds in
/// scope give, and the variables of the body.
#[derive(Clone, Copy)]
pub struct Args<'a> {
    /// The declarations.
    pub decls: &'a dyn Lookup,
    /// The arguments that the bounds in scope give.
    pub scope: &'a [BoundArg],
    /// The variables of the body.
    pub table: &'a Table,
}

impl std::fmt::Debug for Args<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Args")
            .field("scope", &self.scope)
            .finish_non_exhaustive()
    }
}

impl Args<'_> {
    /// The arguments that `ty` gives the parameters of `trait_item`: those its impl gives, or those
    /// of its bound, for a rigid type (traits.trait-arguments and traits.member-types). A trait
    /// without parameters is given none, and the error type gives the error type for each.
    #[must_use]
    pub fn of(&self, ty: &Ty, trait_item: &Item) -> TraitArgs {
        if trait_item.is_record_bound() {
            return self.record_args(ty, trait_item);
        }
        let Some(info) = self.decls.trait_info(trait_item) else {
            return TraitArgs::Known(Vec::new());
        };
        if info.params.is_empty() {
            return TraitArgs::Known(Vec::new());
        }
        match self.table.shape(ty) {
            Ty::Error => TraitArgs::Known(vec![Ty::Error; info.params.len()]),
            Ty::Var(_) | Ty::Value(_) => TraitArgs::Unknown,
            Ty::Con(item, _) => match self.decls.trait_impl(trait_item, &item) {
                Some(imp) => {
                    let targs = self.impl_targs(imp, &self.table.shape(ty));
                    TraitArgs::Known(instantiated(imp, &targs, &imp.trait_args))
                }
                None => TraitArgs::Missing,
            },
            rigid @ (Ty::Param(_) | Ty::SelfTy | Ty::App(..)) => self
                .scope
                .iter()
                .find(|(t, tr, _)| *t == rigid && tr == trait_item)
                .map_or(TraitArgs::Missing, |(_, _, args)| {
                    TraitArgs::Known(args.clone())
                }),
            Ty::Tuple(_) | Ty::Fn(_) | Ty::Spread(_) | Ty::Handler(_) => TraitArgs::Missing,
        }
    }

    /// The types of the fields that the record bound `bound` names, of `ty`: a record's, its
    /// arguments substituted, or a bound's of a rigid type, which names them too
    /// (records.record-bounds). A type without one of them is missing them.
    fn record_args(&self, ty: &Ty, bound: &Item) -> TraitArgs {
        let names = bound.record_fields();
        let fields = match self.table.shape(ty) {
            Ty::Error => return TraitArgs::Known(vec![Ty::Error; names.len()]),
            Ty::Var(_) => return TraitArgs::Unknown,
            t => match self.fields_of(&t) {
                Some(fields) => fields,
                None => return TraitArgs::Missing,
            },
        };
        let found: Option<Vec<Ty>> = names
            .iter()
            .map(|n| fields.iter().find(|(m, _)| m == n).map(|(_, t)| t.clone()))
            .collect();
        found.map_or(TraitArgs::Missing, TraitArgs::Known)
    }

    /// The fields of a record type, its arguments substituted, or those that the record
    /// bounds of a rigid type name.
    #[must_use]
    pub fn fields_of(&self, ty: &Ty) -> Option<Vec<(hir::Name, Ty)>> {
        match ty {
            Ty::Con(item, args) => {
                let info = self.decls.type_info(item)?;
                match &info.def {
                    stilt_hir::decls::TypeDefInfo::Record(fields)
                        if info.params.len() == args.len() =>
                    {
                        Some(
                            fields
                                .iter()
                                .map(|(n, t)| (*n, crate::ty::instantiate(t, &info.params, args)))
                                .collect(),
                        )
                    }
                    _ => None,
                }
            }
            rigid @ (Ty::Param(_) | Ty::SelfTy | Ty::App(..)) => {
                let fields: Vec<(hir::Name, Ty)> = self
                    .scope
                    .iter()
                    .filter(|(t, b, _)| t == rigid && b.is_record_bound())
                    .flat_map(|(_, b, args)| b.record_fields().into_iter().zip(args.clone()))
                    .collect();
                (!fields.is_empty()).then_some(fields)
            }
            _ => None,
        }
    }

    /// The type arguments of an impl's generics, for the type `ty` it is used at: those of the
    /// type's constructor, by their places in the impl's type, and the member types that the
    /// impl's bounds give, from the arguments of those bounds' traits (traits.member-types). A
    /// generic found neither way is the error type.
    #[must_use]
    pub fn impl_targs(&self, imp: &ImplInfo, ty: &Ty) -> Vec<Ty> {
        let args = match (&imp.self_ty, ty) {
            (hir::Ty::Con(_, params), Ty::Con(_, args)) => params
                .iter()
                .zip(args)
                .filter_map(|(p, a)| match p {
                    hir::Ty::Param(v) => Some((v.clone(), a.clone())),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        };
        let mut found: Vec<(GenericId, Ty)> = args;
        // A member type may stand in a bound of another, so each round finds those whose
        // generic is found.
        for _ in 0..=imp.generics.len() {
            let before = found.len();
            for b in &imp.bound_args {
                let Some(arg) = found.iter().find(|(v, _)| *v == b.param).map(|(_, a)| a) else {
                    continue;
                };
                let TraitArgs::Known(given) = self.of(arg, &b.trait_item) else {
                    continue;
                };
                for (written, actual) in b.args.iter().zip(given) {
                    if let hir::Ty::Param(v) = written
                        && !found.iter().any(|(w, _)| w == v)
                    {
                        found.push((v.clone(), actual));
                    }
                }
            }
            if found.len() == before {
                break;
            }
        }
        imp.generics
            .iter()
            .map(|(v, _)| {
                found
                    .iter()
                    .find(|(w, _)| w == v)
                    .map_or(Ty::Error, |(_, t)| t.clone())
            })
            .collect()
    }
}

/// The types `written`, of an impl's declaration, with the impl's generics replaced by
/// `targs`.
#[must_use]
pub fn instantiated(imp: &ImplInfo, targs: &[Ty], written: &[hir::Ty]) -> Vec<Ty> {
    let s = Subst {
        types: imp
            .generics
            .iter()
            .map(|(v, _)| v.clone())
            .zip(targs.iter().cloned())
            .collect(),
        ..Subst::default()
    };
    let table = Table::default();
    written
        .iter()
        .map(|t| table.subst(&s, &Ty::from_hir(t, None)))
        .collect()
}

/// The substitution of a trait's parameters by the arguments `args` that a type gives them.
#[must_use]
pub fn trait_subst(decls: &dyn Lookup, trait_item: &Item, args: &[Ty]) -> Vec<(GenericId, Ty)> {
    decls
        .trait_info(trait_item)
        .map(|info| {
            info.params
                .iter()
                .cloned()
                .zip(args.iter().cloned())
                .collect()
        })
        .unwrap_or_default()
}

/// The arguments the bounds of a signature's type parameters give, as the rigid types of its
/// body see them.
#[must_use]
pub fn scope_of(bound_args: &[stilt_hir::decls::BoundArgs]) -> BoundArgs {
    bound_args
        .iter()
        .map(|b| {
            (
                Ty::Param(b.param.clone()),
                b.trait_item.clone(),
                b.args.iter().map(|a| Ty::from_hir(a, None)).collect(),
            )
        })
        .collect()
}
