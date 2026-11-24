//! The items whose implicit effects an operation inherits (facts.inference): the function it
//! calls, and the impl methods that a trait method or a bound reaches for the types involved.

use stilt_hir::decls::Lookup;
use stilt_hir::decls::{FnSig, ImplInfo, TypeDefInfo};
use stilt_hir::hir::{self, Item, Name};

use super::Key;
use super::alloc::signature_allocates;
use crate::tast::Callee;
use crate::ty::{Ty, instantiate, is_prelude};

/// The pairs of a type constructor and a trait whose structural impl is being followed.
type Visiting<'a> = [(&'a Item, &'a Item)];

/// The names of the methods of a trait, in order.
fn trait_methods(decls: &dyn Lookup, trait_item: &Item) -> Vec<Name> {
    decls.trait_info(trait_item).map_or_else(Vec::new, |info| {
        info.methods.iter().map(|m| m.name).collect()
    })
}

/// Whether the impl writes a method `name` of its own.
fn writes(imp: &ImplInfo, name: &str) -> bool {
    imp.members.iter().any(|m| &*m.name == name)
}

/// traits.structural-calls and traits.show: the method a structural impl calls on each component.
/// Containers show their elements with `show_nested`.
fn component<'a>(trait_item: &Item, name: &'a str) -> &'a str {
    if is_prelude(trait_item, "Show") {
        "show_nested"
    } else {
        name
    }
}

/// The types a structural impl reaches into: the fields or payloads of the type constructor
/// `item` applied to `args`, or the arguments of a built-in type.
pub(crate) fn held(decls: &dyn Lookup, item: &Item, args: &[Ty]) -> Vec<Ty> {
    let Some(info) = decls.type_info(item) else {
        return Vec::new();
    };
    match &info.def {
        TypeDefInfo::Record(fields) => fields
            .iter()
            .map(|(_, t)| instantiate(t, &info.params, args))
            .collect(),
        TypeDefInfo::Variants(vs) => vs
            .iter()
            .flat_map(|(_, payload)| payload.iter().map(|t| instantiate(t, &info.params, args)))
            .collect(),
        TypeDefInfo::Builtin => args.to_vec(),
    }
}

/// The method `name` of an impl of `trait_item` that no source declares, a primitive type's or
/// a structural one, when its result allocates (facts.native-allocation): only `Show`'s do.
fn built_in(decls: &dyn Lookup, trait_item: &Item, name: &str) -> Option<Key> {
    trait_method_sig(decls, trait_item, name)
        .filter(|s| signature_allocates(s))
        .map(|_| Key::BuiltIn(trait_item.clone(), Name::from(name)))
}

/// facts.inference, trait methods: the items that calling the method `name` of `trait_item` on a
/// value of type `ty` names. That is the impl's method, or the trait's default method together with
/// the impl's other methods, which the default calls through `Self`; and the impl methods that the
/// impl's bounds require of the type's arguments. An impl that no source declares names its own
/// method when that allocates (facts.allocation), and a structural one what it calls on each
/// component. A type parameter names nothing, since a call through a bound is a call through a
/// function value (facts.calls-through-function-values), and neither does `Self`, the trait's own
/// parameter.
pub(super) fn method_names(
    decls: &dyn Lookup,
    visiting: &Visiting<'_>,
    trait_item: &Item,
    name: &str,
    ty: &Ty,
) -> Vec<Key> {
    match ty {
        Ty::Param(_)
        | Ty::Handler(_)
        | Ty::SelfTy
        | Ty::App(..)
        | Ty::Var(_)
        | Ty::Value(_)
        | Ty::Error
        | Ty::Fn(_) => Vec::new(),
        Ty::Spread(s) => method_names(decls, visiting, trait_item, name, &s.elem),
        Ty::Tuple(ts) => built_in(decls, trait_item, name)
            .into_iter()
            .chain(ts.iter().flat_map(|t| {
                method_names(decls, visiting, trait_item, component(trait_item, name), t)
            }))
            .collect(),
        Ty::Con(item, args) => match decls.trait_impl(trait_item, item) {
            Some(imp) => {
                let mut called = impl_names(decls, imp, trait_item, item, name);
                called.extend(generic_names(decls, visiting, imp, args));
                called
            }
            None if visiting.contains(&(item, trait_item)) => Vec::new(),
            None => {
                let visiting: Vec<_> = std::iter::once((item, trait_item))
                    .chain(visiting.iter().copied())
                    .collect();
                let components = held(decls, item, args);
                built_in(decls, trait_item, name)
                    .into_iter()
                    .chain(components.iter().flat_map(|t| {
                        method_names(decls, &visiting, trait_item, component(trait_item, name), t)
                    }))
                    .collect()
            }
        },
    }
}

/// The methods that calling `name` through the impl `imp` of `trait_item` for `item` runs: the
/// impl's own, or the trait's default followed by every other method of the trait.
fn impl_names(
    decls: &dyn Lookup,
    imp: &ImplInfo,
    trait_item: &Item,
    item: &Item,
    name: &str,
) -> Vec<Key> {
    let own = |n: &str| {
        if writes(imp, n) {
            Key::ImplMethod(trait_item.clone(), item.clone(), Name::from(n))
        } else {
            Key::DefaultMethod(trait_item.clone(), Name::from(n))
        }
    };
    if writes(imp, name) {
        return vec![own(name)];
    }
    let others = trait_methods(decls, trait_item);
    std::iter::once(name)
        .chain(others.iter().map(|m| &**m).filter(|m| *m != name))
        .map(own)
        .collect()
}

/// Every method of the impl of `trait_item` for `ty`: what a bound requires. An impl's own bounds
/// are required once for all its methods, which keeps a type nested through impls with bounds
/// linear in its depth.
pub(super) fn bound_names(
    decls: &dyn Lookup,
    visiting: &Visiting<'_>,
    trait_item: &Item,
    ty: &Ty,
) -> Vec<Key> {
    let methods = trait_methods(decls, trait_item);
    if let Ty::Con(item, args) = ty
        && let Some(imp) = decls.trait_impl(trait_item, item)
    {
        let mut called: Vec<Key> = (methods.iter())
            .flat_map(|name| impl_names(decls, imp, trait_item, item, name))
            .collect();
        called.extend(generic_names(decls, visiting, imp, args));
        return called;
    }
    (methods.iter())
        .flat_map(|name| method_names(decls, visiting, trait_item, name, ty))
        .collect()
}

/// The impl methods that the bounds of the impl `imp` require of `args`, the arguments of the
/// type it is for.
fn generic_names(
    decls: &dyn Lookup,
    visiting: &Visiting<'_>,
    imp: &ImplInfo,
    args: &[Ty],
) -> Vec<Key> {
    let params: &[hir::Ty] = match &imp.self_ty {
        hir::Ty::Con(_, ps) => ps,
        _ => &[],
    };
    if params.len() != args.len() {
        return Vec::new();
    }
    params
        .iter()
        .zip(args)
        .flat_map(|(param, arg)| match param {
            hir::Ty::Param(v) => imp
                .generics
                .iter()
                .filter(|(w, _)| w == v)
                .flat_map(|(_, traits)| traits.iter())
                .flat_map(|t| bound_names(decls, visiting, t, arg))
                .collect(),
            _ => Vec::new(),
        })
        .collect()
}

/// facts.inference: instantiating a generic function names the impl methods that its bounds require
/// of its type arguments, which are the last of `targs`.
fn instantiation_names(decls: &dyn Lookup, s: Option<&FnSig>, targs: &[Ty]) -> Vec<Key> {
    let Some(s) = s else {
        return Vec::new();
    };
    let (n, m) = (s.type_params.len(), targs.len());
    if m < n {
        return Vec::new();
    }
    s.type_params
        .iter()
        .zip(&targs[m - n..])
        .flat_map(|((_, traits), arg)| traits.iter().map(move |t| (t, arg)))
        .flat_map(|(t, arg)| bound_names(decls, &[], t, arg))
        .collect()
}

/// The signature of the inherent member `name` of `owner`.
pub(super) fn member_sig<'a>(decls: &'a dyn Lookup, owner: &Item, name: &str) -> Option<&'a FnSig> {
    decls
        .inherent_members(owner)
        .iter()
        .find(|m| &*m.name == name)
        .map(|m| &m.signature)
}

/// The signature of the method `name` of a trait.
fn trait_method_sig<'a>(decls: &'a dyn Lookup, trait_item: &Item, name: &str) -> Option<&'a FnSig> {
    decls
        .trait_info(trait_item)?
        .methods
        .iter()
        .find(|m| &*m.name == name)
        .map(|m| &m.signature)
}

/// The item that a call of `c` runs, if it is one with a body: the function, the member, or
/// the impl's method or the trait's default that a trait method on a type with an impl runs,
/// without what its type arguments' bounds name, as a self-call is read
/// (facts.shrinking-recursion).
pub(crate) fn callee_key(decls: &dyn Lookup, c: &Callee) -> Option<Key> {
    match c {
        Callee::Function(item) => Some(Key::Function(item.clone())),
        Callee::Member(owner, name) => Some(Key::Member(owner.clone(), *name)),
        Callee::TraitMethod(trait_item, name, Ty::Con(item, _)) => {
            let imp = decls.trait_impl(trait_item, item)?;
            impl_names(decls, imp, trait_item, item, name)
                .into_iter()
                .next()
        }
        Callee::TraitMethod(..) | Callee::Operation(..) => None,
    }
}

/// The items that a call of `c`, or its use as a value, with the type arguments `targs` names.
pub(crate) fn callee_names(decls: &dyn Lookup, c: &Callee, targs: &[Ty]) -> Vec<Key> {
    match c {
        // An operation runs the nearest handler's body, whose facts count in the function that
        // writes the handler (handlers.implicit-effects-and-capabilities).
        Callee::Operation(..) => Vec::new(),
        Callee::Function(item) => std::iter::once(Key::Function(item.clone()))
            .chain(instantiation_names(decls, decls.function(item), targs))
            .collect(),
        Callee::Member(owner, name) => std::iter::once(Key::Member(owner.clone(), *name))
            .chain(instantiation_names(
                decls,
                member_sig(decls, owner, name),
                targs,
            ))
            .collect(),
        Callee::TraitMethod(trait_item, name, ty) => {
            let mut names = method_names(decls, &[], trait_item, name, ty);
            names.extend(instantiation_names(
                decls,
                trait_method_sig(decls, trait_item, name),
                targs,
            ));
            names
        }
    }
}
