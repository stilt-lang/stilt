//! Which types have a shape, and the types a shape's fields, elements and payloads hold, in the
//! order of meta.shapes.

use stilt_hir::decls::{Lookup, TypeDefInfo};
use stilt_hir::hir::Name;

use crate::ty::{FLOAT_TYPES, INTEGER_TYPES, Ty, instantiate, is_array, is_prelude};

/// How a type holds one of its parts, as E0350 names it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Held {
    Element,
    Key,
    Value,
    /// A tuple's element, by its place.
    Place(usize),
    /// A record's field.
    Field(Name),
    /// A variant's payload field, by its variant and place.
    Payload(Name, usize),
}

impl Held {
    /// The part, as a message says it: "an element of `List<T>`".
    pub(super) fn of(&self, holder: &str) -> String {
        match self {
            Self::Element => format!("an element of `{holder}`"),
            Self::Key => format!("a key of `{holder}`"),
            Self::Value => format!("a value of `{holder}`"),
            Self::Place(i) => format!("element {i} of `{holder}`"),
            Self::Field(f) => format!("the field `{f}` of `{holder}`"),
            Self::Payload(v, i) => format!("payload field {i} of `{holder}`'s variant `{v}`"),
        }
    }
}

/// Whether a type has a shape: one of the cases of meta.shapes. A function type, a handler type and
/// the native types of `std` that no case names have none (meta.types-without-shape). A type
/// parameter, a fresh type and the error type are answered elsewhere, and taken to have one here.
pub(super) fn has_shape(decls: &dyn Lookup, ty: &Ty) -> bool {
    match ty {
        Ty::Fn(_) | Ty::Handler(_) => false,
        Ty::Con(item, _) if item.is_record() => true,
        Ty::Con(item, _) if is_array(item) => true,
        Ty::Con(item, _) if &*item.home == "std.prelude" => {
            let name = &*item.name;
            INTEGER_TYPES.contains(&name)
                || FLOAT_TYPES.contains(&name)
                || ["bool", "str", "Option", "List", "Set", "Map", "Result"].contains(&name)
                || declared(decls, ty)
        }
        Ty::Con(..) => declared(decls, ty),
        Ty::Tuple(_)
        | Ty::Param(_)
        | Ty::SelfTy
        | Ty::App(..)
        | Ty::Spread(_)
        | Ty::Value(_)
        | Ty::Var(_)
        | Ty::Error => true,
    }
}

/// Whether a type constructor is a declared record or variant type.
fn declared(decls: &dyn Lookup, ty: &Ty) -> bool {
    let Ty::Con(item, _) = ty else {
        return false;
    };
    matches!(
        decls.type_info(item).map(|info| &info.def),
        Some(TypeDefInfo::Record(_) | TypeDefInfo::Variants(_))
    )
}

/// The types that the fields, elements and payloads of a type with a shape hold, each with how,
/// in the order of meta.shapes: an option's, a list's, a set's and an array's element, a map's key
/// then value, a tuple's elements, a record's fields in the order of its declaration, or an
/// anonymous record's in alphabetical order, and each variant's payload fields.
pub(super) fn parts(decls: &dyn Lookup, ty: &Ty) -> Vec<(Ty, Held)> {
    match ty {
        Ty::Tuple(ts) => ts
            .iter()
            .enumerate()
            .map(|(i, t)| (t.clone(), Held::Place(i)))
            .collect(),
        Ty::Con(item, args) if item.is_record() => item
            .record_fields()
            .into_iter()
            .zip(args)
            .map(|(f, t)| (t.clone(), Held::Field(f)))
            .collect(),
        Ty::Con(item, args) if is_array(item) => args
            .first()
            .map(|e| vec![(e.clone(), Held::Element)])
            .unwrap_or_default(),
        Ty::Con(item, args)
            if ["Option", "List", "Set"]
                .iter()
                .any(|n| is_prelude(item, n)) =>
        {
            args.iter().map(|t| (t.clone(), Held::Element)).collect()
        }
        Ty::Con(item, args) if is_prelude(item, "Map") && args.len() == 2 => {
            vec![(args[0].clone(), Held::Key), (args[1].clone(), Held::Value)]
        }
        Ty::Con(item, args) => {
            let Some(info) = decls.type_info(item) else {
                return Vec::new();
            };
            match &info.def {
                TypeDefInfo::Record(fields) => fields
                    .iter()
                    .map(|(f, t)| (instantiate(t, &info.params, args), Held::Field(*f)))
                    .collect(),
                TypeDefInfo::Variants(vs) => vs
                    .iter()
                    .flat_map(|(v, payload)| {
                        payload.iter().enumerate().map(|(i, t)| {
                            (instantiate(t, &info.params, args), Held::Payload(*v, i))
                        })
                    })
                    .collect(),
                TypeDefInfo::Builtin => Vec::new(),
            }
        }
        _ => Vec::new(),
    }
}
