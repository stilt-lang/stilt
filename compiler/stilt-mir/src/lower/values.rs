//! Value parameters at run time: each is passed as a hidden argument, in the
//! place of a type parameter's witness, holding its value, so that one instance serves every
//! value, as one `add` serves every modulus of `Mod<p>`. A value parameter of type `i64` may
//! give an array its size, which changes the layout of the values the code holds, so it keys
//! the instance by its value ([`Held::Value`]), as a type parameter keys it by its argument's
//! layout; it is still passed, so that every caller passes the same arguments.

use stilt_hir::decls::Lookup;
use stilt_hir::hir::Value;
use stilt_types::ty::Ty;

use super::Lower;
use crate::items::ImplRef;
use crate::mir::{NumKind, Operand};
use crate::{FnRef, Held};

/// The word that holds a value argument: an integer's bits, or a `bool`'s 0 or 1.
pub(crate) fn value_word(v: &Value) -> u64 {
    match v {
        Value::Int(n) => NumKind::I64.word(*n),
        Value::Bool(b) => u64::from(*b),
    }
}

/// Whether a value parameter's type is `i64`, whose values may give arrays their sizes.
fn sizes(ty: &stilt_hir::hir::Ty) -> bool {
    matches!(ty, stilt_hir::hir::Ty::Con(item, args)
        if args.is_empty() && &*item.home == "std.prelude" && &*item.name == "i64")
}

impl Lower<'_> {
    /// The value that a value argument, or a value parameter that the instance's key gives,
    /// has here.
    pub(crate) fn value_of(&self, ty: &Ty) -> Option<i128> {
        match ty {
            Ty::Value(Value::Int(n)) => Some(*n),
            Ty::Param(_) => self.generic(ty).and_then(|g| g.value),
            _ => None,
        }
    }

    /// The key of a value argument, for a value parameter that keys its instance, or `None`
    /// for a type argument.
    pub(crate) fn value_key(&self, ty: &Ty) -> Option<Held> {
        match ty {
            Ty::Value(Value::Int(n)) => Some(Held::Value(*n)),
            Ty::Value(Value::Bool(_)) => Some(Held::Word),
            Ty::Param(_) => self.generic(ty).and_then(|g| g.value).map(Held::Value),
            _ => None,
        }
    }

    /// The value of the value parameter `ty` reads, as an expression reads it
    /// (generics.value-parameters-in-body): its value where the key gives it, and otherwise its
    /// hidden argument.
    pub(crate) fn value_param(&mut self, ty: &Ty) -> Operand {
        if let Some(n) = self.value_of(ty) {
            return Operand::word(value_word(&Value::Int(n)));
        }
        if let Some(g) = self.generic(ty) {
            return Operand::Local(g.witness);
        }
        self.b.met_error();
        Operand::word(0)
    }

    /// For each of `f`'s generics, in the order of its hidden parameters, whether it is a value
    /// parameter that keys its instances by its value: one of type `i64`.
    pub(crate) fn value_positions(&self, f: &FnRef) -> Vec<bool> {
        let decls = self.decls();
        let g = f.generic();
        let mut out = Vec::new();
        if let FnRef::DefaultMethod(t, _) = g {
            let params = decls.trait_info(t).map_or(0, |i| i.params.len());
            out.extend(std::iter::repeat_n(false, 1 + params));
        }
        let con = match g {
            FnRef::Structural(_, _, crate::items::Shape::Con(item)) => Some(item),
            FnRef::Entry(imp, _) => match &**imp {
                ImplRef::Structural {
                    shape: crate::items::Shape::Con(item),
                    ..
                } => Some(item),
                _ => None,
            },
            _ => None,
        };
        if let Some(info) = con.and_then(|item| decls.type_info(item)) {
            out.extend((0..info.params.len()).map(|i| {
                info.values
                    .iter()
                    .any(|(j, t)| *j as usize == i && sizes(t))
            }));
            return out;
        }
        let (params, values) = match g {
            FnRef::Value(inner) => return self.value_positions(inner),
            FnRef::Entry(imp, _) => match &**imp {
                ImplRef::Written { trait_item, owner } => decls
                    .trait_impl(trait_item, owner)
                    .map(|i| (i.generics.clone(), i.values.clone()))
                    .unwrap_or_default(),
                ImplRef::Structural { .. } => return out,
            },
            FnRef::Method(t, index) => {
                out.push(false);
                decls
                    .trait_info(t)
                    .and_then(|info| info.methods.get(*index as usize).cloned())
                    .map(|m| (m.signature.type_params, m.signature.values))
                    .unwrap_or_default()
            }
            g => super::functions::signature(&decls, g)
                .map(|s| (s.type_params, s.values))
                .unwrap_or_default(),
        };
        out.extend(
            params
                .iter()
                .map(|(p, _)| values.iter().any(|(v, t)| v == p && sizes(t))),
        );
        out
    }
}
