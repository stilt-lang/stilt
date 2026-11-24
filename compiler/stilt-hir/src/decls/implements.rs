//! Whether a type implements a trait, through an impl block or structurally
//! (traits.structural-impls; std.map-key-bounds and traits.hash-follows-written-eq).

use super::signatures::Subst;
use super::{Bounds, Declarations, ImplInfo, TypeDefInfo, TypeInfo, prelude_item};
use crate::hir::{GenericId, Item, Ty};

/// The traits that types implement structurally (traits.structural-impls).
pub(super) fn structural_traits() -> [Item; 4] {
    ["Eq", "Ord", "Hash", "Show"].map(prelude_item)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Answer {
    Yes,
    No,
    Unknown,
}

pub(super) fn all(answers: impl IntoIterator<Item = Answer>) -> Answer {
    let answers: Vec<_> = answers.into_iter().collect();
    if answers.contains(&Answer::No) {
        Answer::No
    } else if answers.contains(&Answer::Unknown) {
        Answer::Unknown
    } else {
        Answer::Yes
    }
}

impl Declarations {
    /// Whether `ty` implements `trait_item`, where the type parameters `bounds` have their
    /// bounds. Through records and variants, a type that is visited again is taken to.
    fn implements_in(
        &self,
        bounds: &Bounds,
        visiting: &[(Item, Item)],
        ty: &Ty,
        trait_item: &Item,
    ) -> Answer {
        let structural = structural_traits().contains(trait_item);
        let each = |ts: &[Ty]| {
            all(ts
                .iter()
                .map(|t| self.implements_in(bounds, visiting, t, trait_item)))
        };
        match ty {
            Ty::Error => Answer::Yes,
            Ty::Param(p) => {
                if bounds
                    .iter()
                    .any(|(v, traits)| v == p && traits.contains(trait_item))
                {
                    Answer::Yes
                } else {
                    Answer::No
                }
            }
            Ty::SelfTy | Ty::App(..) | Ty::Fn(_) | Ty::Handler(_) | Ty::Value(_) => Answer::No,
            // A spread's elements meet a bound when its pattern does, its pack meeting it
            // through its own bounds (variadics.pack-tuples).
            Ty::Spread(_, t) => self.implements_in(bounds, visiting, t, trait_item),
            Ty::Tuple(ts) => {
                if structural {
                    each(ts)
                } else {
                    Answer::No
                }
            }
            Ty::Con(item, args) => self.implements_con(bounds, visiting, item, args, trait_item),
        }
    }

    /// Whether the type constructor `item`, applied to `args`, implements `trait_item`.
    fn implements_con(
        &self,
        bounds: &Bounds,
        visiting: &[(Item, Item)],
        item: &Item,
        args: &[Ty],
        trait_item: &Item,
    ) -> Answer {
        if let Some(impl_info) = self.trait_impl(trait_item, item) {
            return self.implements_by_impl(bounds, visiting, impl_info, args);
        }
        if !structural_traits().contains(trait_item) {
            return Answer::No;
        }
        // traits.hash-follows-written-eq: a written `Eq` takes the automatic `Hash` away.
        if *trait_item == prelude_item("Hash")
            && self.trait_impl(&prelude_item("Eq"), item).is_some()
        {
            return Answer::No;
        }
        if visiting.contains(&(item.clone(), trait_item.clone())) {
            return Answer::Yes;
        }
        match self.types.get(item) {
            Some(info) => {
                self.implements_structurally(bounds, visiting, item, info, args, trait_item)
            }
            None => Answer::Yes,
        }
    }

    /// Whether `args` meet the bounds of an impl block's type parameters.
    fn implements_by_impl(
        &self,
        bounds: &Bounds,
        visiting: &[(Item, Item)],
        impl_info: &ImplInfo,
        args: &[Ty],
    ) -> Answer {
        let params = match &impl_info.self_ty {
            Ty::Con(_, params) => params.as_slice(),
            _ => &[],
        };
        let arg_of = |v: &GenericId| {
            params
                .iter()
                .zip(args)
                .find_map(|(param, arg)| (*param == Ty::Param(v.clone())).then_some(arg))
        };
        all(impl_info.generics.iter().flat_map(|(v, traits)| {
            arg_of(v).into_iter().flat_map(move |arg| {
                traits
                    .iter()
                    .map(move |t| self.implements_in(bounds, visiting, arg, t))
            })
        }))
    }

    /// traits.structural-impls: a type implements a structural trait when all it holds does.
    fn implements_structurally(
        &self,
        bounds: &Bounds,
        visiting: &[(Item, Item)],
        item: &Item,
        info: &TypeInfo,
        args: &[Ty],
        trait_item: &Item,
    ) -> Answer {
        // A value argument is no type, and holds no trait (generics.array-traits).
        let each = |ts: &[Ty]| {
            all((0..)
                .zip(ts)
                .filter(|(i, _)| !info.values.iter().any(|(v, _)| v == i))
                .map(|(_, t)| self.implements_in(bounds, visiting, t, trait_item)))
        };
        let mut inside = visiting.to_vec();
        inside.push((item.clone(), trait_item.clone()));
        let holds = |t: &Ty| {
            let t = if info.params.len() == args.len() {
                let types = info.params.iter().cloned().zip(args.iter().cloned());
                Subst {
                    types: types.collect(),
                    ..Subst::default()
                }
                .ty(t)
            } else {
                Ty::Error
            };
            self.implements_in(bounds, &inside, &t, trait_item)
        };
        match &info.def {
            // std.map-key-bounds: comparing maps finds keys, so it needs the key type's `Hash` too.
            TypeDefInfo::Builtin if &*item.name == "Map" && *trait_item == prelude_item("Eq") => {
                let hash = |key| self.implements_in(bounds, visiting, key, &prelude_item("Hash"));
                all([each(args), args.first().map_or(Answer::Yes, hash)])
            }
            TypeDefInfo::Builtin if builtin_has(item, trait_item) => each(args),
            TypeDefInfo::Builtin => Answer::No,
            TypeDefInfo::Record(fields) => all(fields.iter().map(|(_, t)| holds(t))),
            TypeDefInfo::Variants(variants) => all(variants
                .iter()
                .flat_map(|(_, payload)| payload.iter().map(holds))),
        }
    }

    pub(super) fn implements(&self, bounds: &Bounds, ty: &Ty, trait_item: &Item) -> Answer {
        self.implements_in(bounds, &[], ty, trait_item)
    }

    /// traits.structural-impls: whether a type constructor has a structural impl of a trait,
    /// which it has when its type would implement it with every type parameter implementing
    /// it.
    pub(super) fn structural_impl(&self, item: &Item, trait_item: &Item) -> bool {
        structural_traits().contains(trait_item)
            && self.types.get(item).is_some_and(|info| {
                let bounds = info
                    .params
                    .iter()
                    .map(|v| (v.clone(), vec![trait_item.clone()]))
                    .collect();
                let ty = Ty::Con(
                    item.clone(),
                    info.params.iter().cloned().map(Ty::Param).collect(),
                );
                self.implements(&bounds, &ty, trait_item) == Answer::Yes
            })
    }
}

/// traits.structural-impls and traits.floats: floats have no `Hash`, and maps no `Ord` or `Hash`;
/// views.iterator-traits: iterators have none, and polymorphism.lazy-values: nor do lazy values.
fn builtin_has(item: &Item, trait_item: &Item) -> bool {
    match &*item.name {
        "f32" | "f64" => *trait_item != prelude_item("Hash"),
        "Map" => *trait_item == prelude_item("Eq") || *trait_item == prelude_item("Show"),
        // views.iterator-traits: iterators have none of the structural traits.
        "Iter" if &*item.home == "std.view" => false,
        "Lazy" if &*item.home == "std.lazy" => false,
        _ => true,
    }
}
