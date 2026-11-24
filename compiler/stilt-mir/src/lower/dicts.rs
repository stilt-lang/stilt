//! Dictionaries: what generic code calls a type's trait methods through.
//!
//! A dictionary is a data object: first the code of each of the trait's methods, as the
//! impl's entries, compiled for the layouts of the impl's type arguments, then the impl's
//! environment, its type arguments. Its tag is 0, but for the
//! structural `Ord` of an integer type, whose tag tells the runtime that its keys' order is
//! that of integers, signed or not ([`crate::mir::SIGNED_ORDER`]), so that a sort compares them
//! itself rather than through the dictionary (goal debug-speed), and for the structural `Eq`
//! and `Hash` of an integer type, `bool` and `str`, whose tags tell a map to hash and compare
//! its keys itself ([`crate::mir::WORD_KEYS`]), since those impls run no code of the program
//! (std.maps). A written impl's
//! environment holds, for each of its generics, a witness, then a dictionary for each bound. A
//! structural impl's holds, for each type argument, a witness, then a dictionary for each of
//! the prelude's traits `Eq`, `Ord`, `Hash` and `Show` that the argument implements, or 0, so
//! that it can build the dictionary of any component it reaches. A view's holds the viewed
//! type's witness, then the dictionaries of the viewed list's elements, or 0 for a view of a
//! string, which the runtime compares, hashes and shows in place (views.functions-of-views). A
//! dictionary whose parts are all known is static data.

use stilt_hir::decls::{Lookup, prelude_item};
use stilt_hir::hir::Item;
use stilt_types::ty::Ty;

use super::Lower;
use crate::FnRef;
use crate::items::ImplRef;
use crate::mir::{Const, Heapness, Operand, SIGNED_ORDER, STR_KEYS, UNSIGNED_ORDER, WORD_KEYS};
use crate::repr::num_kind;

/// The prelude's traits, in the order of a structural environment.
pub(crate) const PRELUDE_TRAITS: [&str; 4] = ["Eq", "Ord", "Hash", "Show"];

impl Lower<'_> {
    /// The dictionary of a type for a trait, or 0 when the type has none.
    pub(crate) fn dict(&mut self, ty: &Ty, t: &Item) -> Operand {
        if let Some(g) = self.generic(ty) {
            if let Some((_, d)) = g.dicts.iter().find(|(tr, _)| tr == t) {
                return d.clone();
            }
            // A type that crosses into code past the caps is given dictionaries that forward to
            // its own (`super::bridge`).
            return match self.crossing_of(ty) {
                Some(inner) => self.forward_dict(&inner, t),
                None => Operand::word(0),
            };
        }
        let Some(imp) = self.impl_of(t, ty) else {
            return Operand::word(0);
        };
        let env = self.impl_env(&imp, ty);
        self.impl_dict(&imp, ty, env)
    }

    /// The dictionary of an impl for the type `ty` it is used at, whose environment is `env`.
    pub(crate) fn impl_dict(
        &mut self,
        imp: &ImplRef,
        ty: &Ty,
        env: Vec<(Operand, Heapness)>,
    ) -> Operand {
        let (ImplRef::Written { trait_item: t, .. } | ImplRef::Structural { trait_item: t, .. }) =
            imp;
        let methods = self
            .decls()
            .trait_info(t)
            .map_or(0, |info| info.methods.len());
        let targs = self.impl_type_args(imp, ty);
        let mut fields: Vec<(Operand, Heapness)> = (0..methods)
            .map(|i| {
                let entry = FnRef::Entry(
                    Box::new(imp.clone()),
                    u32::try_from(i).expect("under 4G methods"),
                );
                let entry = self.instance(entry, &targs);
                (Operand::Const(Const::Code(entry)), Heapness::Static(false))
            })
            .collect();
        fields.extend(env);
        self.alloc(dict_tag(imp, ty), fields)
    }

    /// The type arguments of an impl's generics, for the type `ty` it is used at: a written
    /// impl's, or a structural impl's constructor's arguments.
    pub(crate) fn impl_type_args(&self, imp: &ImplRef, ty: &Ty) -> Vec<Ty> {
        match imp {
            ImplRef::Written { trait_item, owner } => self
                .decls()
                .trait_impl(trait_item, owner)
                .map(|info| self.impl_targs(info, ty))
                .unwrap_or_default(),
            ImplRef::Structural { .. } => match ty {
                _ if super::packs::is_dynamic_tuple(ty) => Vec::new(),
                Ty::Con(_, args) | Ty::Tuple(args) => args.clone(),
                _ => Vec::new(),
            },
        }
    }

    /// The environment of an impl, for the type `ty` it is used at.
    pub(crate) fn impl_env(&mut self, imp: &ImplRef, ty: &Ty) -> Vec<(Operand, Heapness)> {
        match imp {
            ImplRef::Written { trait_item, owner } => {
                let Some(info) = self.decls().trait_impl(trait_item, owner).cloned() else {
                    return Vec::new();
                };
                let targs = self.impl_targs(&info, ty);
                let mut env = Vec::new();
                for ((_, traits), arg) in info.generics.iter().zip(&targs) {
                    env.push((self.witness(arg), Heapness::Static(false)));
                    for t in traits {
                        env.push((self.dict(arg, t), Heapness::Static(true)));
                    }
                }
                // The descriptors of the arguments its methods reflect on
                // (meta.unseen-instantiations).
                for g in self.impl_described(trait_item, owner) {
                    let at = info.generics.iter().position(|(h, _)| *h == g);
                    let arg = at.and_then(|k| targs.get(k)).cloned().unwrap_or(Ty::Error);
                    env.push((self.descriptor(&arg), Heapness::Static(true)));
                }
                env
            }
            ImplRef::Structural { .. } => self.structural_env(ty),
        }
    }

    /// The environment of a structural impl, for the type `ty` it is used at.
    pub(crate) fn structural_env(&mut self, ty: &Ty) -> Vec<(Operand, Heapness)> {
        if super::packs::is_dynamic_tuple(ty) {
            return self.pack_env(ty);
        }
        let args = match ty {
            Ty::Con(item, args) => match super::packs::components(&self.decls(), item, args) {
                Some(components) => components,
                None => return self.type_pack_env(args),
            },
            Ty::Tuple(args) => args.clone(),
            _ => Vec::new(),
        };
        let view = ty.viewed().is_some();
        let mut env = Vec::new();
        for arg in &args {
            env.push((self.witness(arg), Heapness::Static(false)));
            // A view's component is an element of the viewed list, if it views one.
            let component = if view {
                arg.listed().cloned()
            } else {
                Some(arg.clone())
            };
            for name in PRELUDE_TRAITS {
                let t = prelude_item(name);
                let d = match &component {
                    Some(c) if self.implements(c, &t) => self.dict(c, &t),
                    _ => Operand::word(0),
                };
                env.push((d, Heapness::Static(true)));
            }
        }
        env
    }
}

impl Lower<'_> {
    /// The environment of the structural impl of a tuple that spreads a pack whose length is
    /// known at run time only, and the part of one of a type with such a pack that stands for
    /// it: in place of an argument's witness and dictionaries, the list of the elements'
    /// witnesses and the lists of their dictionaries, 0 for an element without the impl.
    pub(crate) fn pack_env(&mut self, ty: &Ty) -> Vec<(Operand, Heapness)> {
        let Ty::Tuple(ts) = ty else {
            return Vec::new();
        };
        let ts = stilt_types::ty::Table::default().elements(ts);
        let traits: Vec<Item> = PRELUDE_TRAITS.iter().map(|n| prelude_item(n)).collect();
        let (witnesses, lists) = self.dynamic_lists(&ts, &traits);
        std::iter::once(witnesses)
            .chain(lists)
            .map(|l| (l, Heapness::Static(true)))
            .collect()
    }
}

/// The tag of an impl's dictionary for the type `ty`: the order of integers, signed or not,
/// for the structural `Ord` of an integer type; keys of one word for the structural `Eq` and
/// `Hash` of an integer type or `bool`, and keys that are strings for those of `str`; and
/// otherwise 0.
fn dict_tag(imp: &ImplRef, ty: &Ty) -> u16 {
    let ImplRef::Structural { trait_item, .. } = imp else {
        return 0;
    };
    let keys = *trait_item == prelude_item("Eq") || *trait_item == prelude_item("Hash");
    match num_kind(ty) {
        Some(kind) if kind.is_float() => 0,
        Some(kind) if *trait_item == prelude_item("Ord") => {
            if kind.is_signed() {
                SIGNED_ORDER
            } else {
                UNSIGNED_ORDER
            }
        }
        Some(_) if keys => WORD_KEYS,
        None if keys && ty.is_prelude("bool") => WORD_KEYS,
        None if keys && ty.is_prelude("str") => STR_KEYS,
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use stilt_hir::decls::prelude_item;
    use stilt_types::ty::Ty;

    use super::dict_tag;
    use crate::items::{ImplRef, Shape};
    use crate::mir::{SIGNED_ORDER, STR_KEYS, UNSIGNED_ORDER, WORD_KEYS};

    /// The tag of the structural impl of the prelude's trait `name` for the prelude's type `ty`.
    fn structural(name: &str, ty: &str) -> u16 {
        let shape = Shape::Con(prelude_item(ty));
        dict_tag(
            &ImplRef::Structural {
                trait_item: prelude_item(name),
                shape,
            },
            &Ty::named(ty),
        )
    }

    #[test]
    fn the_runtime_orders_and_keys_integers_bools_and_strings_by_their_dictionaries_tags() {
        assert_eq!(structural("Ord", "i64"), SIGNED_ORDER);
        assert_eq!(structural("Ord", "i8"), SIGNED_ORDER);
        assert_eq!(structural("Ord", "u8"), UNSIGNED_ORDER);
        assert_eq!(structural("Ord", "u64"), UNSIGNED_ORDER);
        assert_eq!(structural("Eq", "u32"), WORD_KEYS);
        assert_eq!(structural("Hash", "i64"), WORD_KEYS);
        assert_eq!(structural("Eq", "bool"), WORD_KEYS);
        assert_eq!(structural("Hash", "str"), STR_KEYS);
    }

    #[test]
    fn every_other_dictionary_has_no_tag() {
        assert_eq!(structural("Ord", "f64"), 0);
        assert_eq!(structural("Eq", "f32"), 0);
        assert_eq!(structural("Ord", "str"), 0);
        assert_eq!(structural("Ord", "bool"), 0);
        assert_eq!(structural("Show", "i64"), 0);
        let written = ImplRef::Written {
            trait_item: prelude_item("Ord"),
            owner: prelude_item("i64"),
        };
        assert_eq!(dict_tag(&written, &Ty::named("i64")), 0);
    }
}
