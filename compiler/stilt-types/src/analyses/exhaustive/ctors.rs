//! The constructors that build the values of a type, the types of their fields, and whether a
//! type has values at all (patterns.types-without-values).

use std::collections::HashSet;

use stilt_hir::decls::Lookup;
use stilt_hir::decls::{TypeDefInfo, TypeInfo};
use stilt_hir::hir::{self, GenericId, Item, Name};

use super::Ctor;
use crate::ty::{SHAPE_CASES, Ty, case_payload, instantiate, is_meta, meta_item};

/// A type with an error, or one that inference left open because it met an error: only such
/// variables are left in a body without errors.
pub(super) fn is_error(ty: &Ty) -> bool {
    matches!(ty, Ty::Error | Ty::Var(_))
}

/// Whether a type is a list, whose values the algorithm splits by length.
pub(super) fn is_list(ty: &Ty) -> bool {
    ty.is_prelude("List")
}

/// The size of an array type whose size is a value of 0 or more (generics.array-exhaustiveness).
pub(super) fn array_size(ty: &Ty) -> Option<usize> {
    match ty.arrayed() {
        Some((_, Ty::Value(hir::Value::Int(k)))) => usize::try_from(*k).ok(),
        _ => None,
    }
}

/// The fields of a record type, in declaration order, or none if the type isn't a record.
pub(super) fn record_fields(decls: &dyn Lookup, item: &Item) -> Vec<Name> {
    match decls.type_info(item).map(|info| &info.def) {
        Some(TypeDefInfo::Record(fields)) => fields.iter().map(|(f, _)| *f).collect(),
        _ => Vec::new(),
    }
}

/// The types of a constructor's fields, for a value of type `ty`.
pub(super) fn field_types(decls: &dyn Lookup, ty: &Ty, ctor: &Ctor) -> Vec<Ty> {
    match (ctor, ty) {
        // A case of a shape has one payload, an accessor of a native type, whose fresh types
        // matter to no pattern (meta.shape-accessors).
        (Ctor::Variant(v), Ty::Con(owner, args)) if is_meta(owner, "Shape") && args.len() == 1 => {
            case_payload(&v.name, &args[0], &mut |_| Ty::Error)
                .into_iter()
                .collect()
        }
        (Ctor::Variant(v), Ty::Con(owner, args)) => {
            match (decls.variant(v), decls.type_info(owner)) {
                (Some(variant), Some(info)) => variant
                    .payload
                    .iter()
                    .map(|t| instantiate(t, &info.params, args))
                    .collect(),
                _ => Vec::new(),
            }
        }
        (Ctor::Tuple(_), Ty::Tuple(ts)) => ts.clone(),
        // An array is matched as a tuple of its size (generics.array-patterns).
        (Ctor::Array(n), Ty::Con(..)) if ty.arrayed().is_some() => {
            vec![ty.arrayed().map_or(Ty::Error, |(elem, _)| elem.clone()); *n]
        }
        (Ctor::Record(item, fields), Ty::Con(_, args)) => match decls.type_info(item) {
            Some(
                info @ TypeInfo {
                    def: TypeDefInfo::Record(declared),
                    ..
                },
            ) => fields
                .iter()
                // The fields are the record's own, so each is found.
                .filter_map(|f| declared.iter().find(|(d, _)| d == f))
                .map(|(_, t)| instantiate(t, &info.params, args))
                .collect(),
            _ => Vec::new(),
        },
        (Ctor::Len(n) | Ctor::AtLeast(n), Ty::Con(_, args)) if args.len() == 1 => {
            vec![args[0].clone(); *n]
        }
        _ => Vec::new(),
    }
}

/// The number of a constructor's fields, for a value of type `ty`.
pub(super) fn arity(decls: &dyn Lookup, ty: &Ty, ctor: &Ctor) -> usize {
    field_types(decls, ty, ctor).len()
}

/// The constructors that build the values of a type, when they are finitely many, in
/// declaration order. Lists are split by length separately.
pub(super) fn all_ctors(decls: &dyn Lookup, ty: &Ty) -> Option<Vec<Ctor>> {
    let live = |ctors: Vec<Ctor>| -> Vec<Ctor> {
        ctors
            .into_iter()
            .filter(|c| {
                field_types(decls, ty, c)
                    .iter()
                    .all(|t| inhabited(decls, t))
            })
            .collect()
    };
    match ty {
        // A tuple whose arity isn't known has no constructor a pattern could name
        // (variadics.pack-tuples).
        Ty::Tuple(_) if ty.is_pack_tuple() => None,
        Ty::Tuple(ts) => Some(live(vec![Ctor::Tuple(ts.len())])),
        _ if ty.is_prelude("bool") => Some(vec![Ctor::Bool(false), Ctor::Bool(true)]),
        _ if ty.is_prelude("Never") => Some(Vec::new()),
        // An array is one tuple of its size, and one of a negative size has no values
        // (generics.array-sizes and generics.array-patterns).
        Ty::Con(..) if ty.arrayed().is_some() => match ty.arrayed() {
            Some((_, Ty::Value(hir::Value::Int(k)))) if *k < 0 => Some(Vec::new()),
            _ => array_size(ty).map(|k| live(vec![Ctor::Array(k)])),
        },
        // The cases of a shape, a native variant type (meta.std-meta and meta.shapes).
        Ty::Con(item, _) if is_meta(item, "Shape") => Some(
            SHAPE_CASES
                .iter()
                .map(|case| Ctor::Variant(meta_item(case)))
                .collect(),
        ),
        Ty::Con(item, _) => match decls.type_info(item).map(|info| &info.def) {
            Some(TypeDefInfo::Variants(vs)) => Some(live(
                vs.iter()
                    .map(|(name, _)| {
                        Ctor::Variant(Item {
                            home: item.home,
                            name: *name,
                        })
                    })
                    .collect(),
            )),
            Some(TypeDefInfo::Record(fields)) => Some(live(vec![Ctor::Record(
                item.clone(),
                fields.iter().map(|(f, _)| *f).collect(),
            )])),
            Some(TypeDefInfo::Builtin) | None => None,
        },
        Ty::Param(_)
        | Ty::Handler(_)
        | Ty::SelfTy
        | Ty::App(..)
        | Ty::Fn(_)
        | Ty::Spread(_)
        | Ty::Var(_)
        | Ty::Value(_)
        | Ty::Error => None,
    }
}

/// A declared type constructor, with which of its arguments have values.
type Pair = (Item, Vec<bool>);

/// The pairs that [`inhabited`] has met, and those it has shown to have values.
struct Inhabited<'a> {
    decls: &'a dyn Lookup,
    met: HashSet<Pair>,
    shown: HashSet<Pair>,
}

/// patterns.algorithm, as patterns.types-without-values states it: the types that have values are
/// the smallest set such that a type has values when one of its constructors has fields whose types
/// all have values. Whether a declared type has values depends only on which of its arguments have
/// values, so the set is built over pairs of a type constructor and that choice, which are finitely
/// many: each pair met is tried with its arguments standing for `()` or `Never`, until no try adds
/// a pair. The order in which a round tries the pairs changes only the rounds it takes: a pair is
/// shown only when it has values, and the last round leaves unshown only pairs that need one
/// another to have values.
fn inhabited(decls: &dyn Lookup, ty: &Ty) -> bool {
    let mut state = Inhabited {
        decls,
        met: HashSet::new(),
        shown: HashSet::new(),
    };
    loop {
        let size = (state.met.len(), state.shown.len());
        let answer = state.has_values(ty);
        let pairs: Vec<Pair> = state.met.iter().cloned().collect();
        for (item, has) in pairs {
            let args: Vec<Ty> = has
                .iter()
                .map(|&b| if b { Ty::unit() } else { Ty::never() })
                .collect();
            if state.builds(&item, &args) {
                state.shown.insert((item, has));
            }
        }
        if (state.met.len(), state.shown.len()) == size {
            return answer;
        }
    }
}

impl Inhabited<'_> {
    /// Whether a type has values, as far as the pairs shown so far tell, meeting every pair it
    /// reads.
    fn has_values(&mut self, ty: &Ty) -> bool {
        let decls = self.decls;
        match ty {
            _ if ty.is_prelude("Never") => false,
            Ty::Tuple(ts) => ts.iter().all(|t| self.has_values(t)),
            Ty::Con(item, args) => match decls.type_info(item).map(|info| &info.def) {
                Some(TypeDefInfo::Variants(_) | TypeDefInfo::Record(_)) => {
                    let pair = (
                        item.clone(),
                        args.iter().map(|t| self.has_values(t)).collect(),
                    );
                    let shown = self.shown.contains(&pair);
                    self.met.insert(pair);
                    shown
                }
                Some(TypeDefInfo::Builtin) | None => true,
            },
            Ty::Param(_)
            | Ty::Handler(_)
            | Ty::SelfTy
            | Ty::App(..)
            | Ty::Fn(_)
            | Ty::Spread(_)
            | Ty::Var(_)
            | Ty::Value(_)
            | Ty::Error => true,
        }
    }

    /// Whether one of the constructors of `item`, applied to `args`, has fields whose types all
    /// have values.
    fn builds(&mut self, item: &Item, args: &[Ty]) -> bool {
        let decls = self.decls;
        let Some(info) = decls.type_info(item) else {
            return true;
        };
        match &info.def {
            TypeDefInfo::Variants(vs) => vs
                .iter()
                .any(|(_, payload)| self.all_have_values(&info.params, args, payload)),
            TypeDefInfo::Record(fields) => {
                self.all_have_values(&info.params, args, fields.iter().map(|(_, t)| t))
            }
            TypeDefInfo::Builtin => true,
        }
    }

    /// Whether the field types `ts`, with `params` replaced by `args`, all have values.
    fn all_have_values<'t>(
        &mut self,
        params: &[GenericId],
        args: &[Ty],
        ts: impl IntoIterator<Item = &'t hir::Ty>,
    ) -> bool {
        ts.into_iter()
            .all(|t| self.has_values(&instantiate(t, params, args)))
    }
}
