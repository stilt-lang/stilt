//! Where a body meets a bound (meta.types-without-shape and meta.unseen-instantiations): an impl's
//! own type parameters are checked there, as a trait impl's bounds are, so a call that needs an
//! impl of a trait for a type uses the impl's methods at the impl's type arguments for that type,
//! which the fixed point of `reflects` and E0350 read as they read a call of a function. A body
//! that meets a bound with one of its own type parameters in the impl's arguments reflects on it
//! instead, and its callers give its descriptor.

use stilt_hir::decls::Lookup;
use stilt_hir::hir::{GenericId, Item, Name};
use stilt_syntax::TextRange;

use super::Key;
use super::summary::{Summary, Use, of_self};
use crate::params::{Args, TraitArgs};
use crate::ty::{Table, Ty};

/// How deep bounds are followed through the impls that need them.
const DEPTH: usize = 8;

/// The call or the name where a bound is met, and the call's arguments, each with its type, at the
/// first of which whose type holds a type without a shape E0350 is reported
/// (meta.types-without-shape).
pub(super) type Site<'a> = (TextRange, &'a [(TextRange, Ty)]);

/// Records that the body meets the bound `t` for the type `ty` at `site`: the uses of the
/// methods of `ty`'s impl of `t`, and the bounds that the impl's own type parameters need,
/// through structural impls to the types they hold.
pub(super) fn met(decls: &dyn Lookup, s: &mut Summary, (t, ty): (&Item, &Ty), site: Site<'_>) {
    meet(decls, s, (t, ty), site, 0);
}

fn meet(decls: &dyn Lookup, s: &mut Summary, (t, ty): (&Item, &Ty), site: Site<'_>, depth: usize) {
    if depth > DEPTH {
        return;
    }
    let args = match ty {
        Ty::Con(item, args) => {
            if let Some(info) = decls.trait_impl(t, item) {
                let table = Table::default();
                let found = Args {
                    decls,
                    scope: &[],
                    table: &table,
                }
                .impl_targs(info, ty);
                let targs: Vec<_> = info
                    .generics
                    .iter()
                    .map(|(g, _)| g.clone())
                    .zip(found.iter().cloned())
                    .collect();
                for m in &info.members {
                    s.uses.push(Use {
                        callee: Key::ImplMethod(t.clone(), item.clone(), m.name),
                        targs: targs.clone(),
                        at: site.0,
                        args: site.1.to_vec(),
                        poly: false,
                    });
                }
                defaults_used(decls, s, (t, ty), site);
                for ((_, bounds), x) in info.generics.iter().zip(&found) {
                    for b in bounds {
                        meet(decls, s, (b, x), site, depth + 1);
                    }
                }
                return;
            }
            args
        }
        Ty::Tuple(ts) => ts,
        _ => return,
    };
    // A structural impl needs the trait of each type the constructor applies
    // (traits.structural-impls).
    for a in args {
        meet(decls, s, (t, a), site, depth + 1);
    }
}

/// Records that the body builds the dictionary of `t` for `ty`, or calls one of its methods,
/// which may call any of the trait's default methods with `Self` and the trait's parameters
/// that `ty` gives. What any default reads of them is the trait's ([`super::of_defaults`]), so
/// that a dictionary's entries and every call pass the same descriptors.
fn defaults_used(decls: &dyn Lookup, s: &mut Summary, (t, ty): (&Item, &Ty), site: Site<'_>) {
    let has_default = decls
        .trait_info(t)
        .is_some_and(|i| i.methods.iter().any(|m| m.has_default));
    if !has_default {
        return;
    }
    let targs = trait_given(decls, s, (t, ty));
    s.uses.push(Use {
        callee: super::of_defaults(t),
        targs,
        at: site.0,
        args: site.1.to_vec(),
        poly: false,
    });
}

/// Records a call of trait `t`'s method `name` on a value of type `ty`, at the method's own
/// type arguments `targs`. The facts of the trait's method, keyed as its default, hold what
/// any impl's method reads of its own type parameters, besides what its default reads, so that
/// a call through a bound, which can't see the impl, passes their descriptors.
pub(super) fn method_used(
    decls: &dyn Lookup,
    s: &mut Summary,
    (t, name, ty): (&Item, Name, &Ty),
    (targs, site): (&[Ty], Site<'_>),
) {
    let Some(m) = decls
        .trait_info(t)
        .and_then(|i| i.methods.iter().find(|m| m.name == name))
    else {
        return;
    };
    let own: Vec<_> = m
        .signature
        .type_params
        .iter()
        .map(|(g, _)| g.clone())
        .collect();
    defaults_used(decls, s, (t, ty), site);
    if own.is_empty() {
        return;
    }
    s.uses.push(Use {
        callee: Key::DefaultMethod(t.clone(), name),
        targs: own
            .into_iter()
            .zip(targs.iter().map(|x| of_self(s, x)))
            .collect(),
        at: site.0,
        args: site.1.to_vec(),
        poly: false,
    });
}

/// What a type gives a trait's default methods: `Self`, and the trait's parameters where its
/// impl gives them.
fn trait_given(decls: &dyn Lookup, s: &Summary, (t, ty): (&Item, &Ty)) -> Vec<(GenericId, Ty)> {
    let mut given = vec![(super::self_param(), of_self(s, ty))];
    let table = Table::default();
    let args = Args {
        decls,
        scope: &[],
        table: &table,
    };
    if let TraitArgs::Known(found) = args.of(ty, t) {
        let params = decls.trait_info(t).map(|i| i.params.clone());
        let found = found.iter().map(|a| of_self(s, a));
        given.extend(params.unwrap_or_default().into_iter().zip(found));
    }
    given
}

/// In a method of a trait's impl, each of its own type parameters, with the trait method's
/// that it stands for.
pub(super) fn own_of_trait(decls: &dyn Lookup, key: &Key) -> Vec<(GenericId, GenericId)> {
    let Key::ImplMethod(t, owner, name) = key else {
        return Vec::new();
    };
    let own = decls
        .trait_impl(t, owner)
        .and_then(|i| i.members.iter().find(|m| m.name == *name));
    let of_trait = decls
        .trait_info(t)
        .and_then(|i| i.methods.iter().find(|m| m.name == *name));
    let (Some(own), Some(of_trait)) = (own, of_trait) else {
        return Vec::new();
    };
    // The method's signature holds the impl's type parameters before its own.
    own.signature
        .type_params
        .iter()
        .filter(|(g, _)| g.owner.member.is_some())
        .zip(&of_trait.signature.type_params)
        .map(|((a, _), (b, _))| (a.clone(), b.clone()))
        .collect()
}
