//! The native types of `std.meta` (meta.std-meta): the native variant type `Shape<T>`, whose
//! cases meta.shapes lists, and the types of their accessors.

use stilt_hir::hir::{Item, Name};

use super::Ty;

/// The module of reflection.
pub const META: &str = "std.meta";

/// The cases of `Shape<T>`, in the order of meta.shapes, which exhaustiveness lists them in.
pub const SHAPE_CASES: [&str; 13] = [
    "Int", "Float", "Bool", "Str", "Unit", "Option", "List", "Set", "Map", "Array", "Tuple",
    "Record", "Variants",
];

/// Whether a type constructor is `std.meta`'s `name`.
#[must_use]
pub fn is_meta(item: &Item, name: &str) -> bool {
    &*item.home == META && &*item.name == name
}

/// `std.meta`'s item `name`: one of its types, or a case of `Shape`.
#[must_use]
pub fn meta_item(name: &str) -> Item {
    Item {
        home: Name::from(META),
        name: Name::from(name),
    }
}

/// Whether an item is a case of `Shape`, as a pattern names it.
#[must_use]
pub fn is_shape_case(item: &Item) -> bool {
    &*item.home == META && SHAPE_CASES.contains(&&*item.name)
}

/// `meta.name<args…>`.
#[must_use]
pub fn meta_ty(name: &str, args: Vec<Ty>) -> Ty {
    Ty::Con(meta_item(name), args)
}

/// The type of the payload of the case `case` of a `Shape<T>`, its fresh types made by `fresh`,
/// which takes the letter that names each in meta.shapes's table: `E`, `K` or `V`
/// (meta.fresh-types).
#[must_use]
pub fn case_payload(case: &str, t: &Ty, fresh: &mut dyn FnMut(char) -> Ty) -> Option<Ty> {
    let convert = |u: Ty| meta_ty("Convert", vec![t.clone(), u]);
    Some(match case {
        "Int" => meta_ty("Integer", vec![t.clone()]),
        "Float" => convert(Ty::f64()),
        "Bool" => convert(Ty::bool()),
        "Str" => convert(Ty::str()),
        "Unit" => convert(Ty::unit()),
        "Option" => convert(Ty::option(fresh('E'))),
        "List" | "Set" => convert(Ty::list(fresh('E'))),
        "Map" => {
            let (k, v) = (fresh('K'), fresh('V'));
            convert(Ty::list(Ty::Tuple(vec![k, v])))
        }
        "Array" => meta_ty("Sized", vec![t.clone(), fresh('E')]),
        "Tuple" | "Record" => meta_ty("Fields", vec![t.clone()]),
        "Variants" => meta_ty("Cases", vec![t.clone()]),
        _ => return None,
    })
}

impl Ty {
    /// The type `T` of a `meta.name<T, …>`.
    #[must_use]
    pub fn meta_of(&self, name: &str) -> Option<&Ty> {
        match self {
            Self::Con(item, args) if is_meta(item, name) => args.first(),
            _ => None,
        }
    }

    /// Whether the type holds one of the fresh types of shapes (meta.fresh-types).
    #[must_use]
    pub fn holds_fresh(&self, fresh: &dyn Fn(&stilt_hir::hir::GenericId) -> bool) -> bool {
        match self {
            Self::Param(g) => fresh(g),
            Self::Con(_, ts) | Self::Tuple(ts) => ts.iter().any(|t| t.holds_fresh(fresh)),
            Self::App(head, ts) => {
                head.holds_fresh(fresh) || ts.iter().any(|t| t.holds_fresh(fresh))
            }
            Self::Fn(f) => {
                f.params.iter().any(|(_, t)| t.holds_fresh(fresh))
                    || f.ret.holds_fresh(fresh)
                    || f.row.raise.as_deref().is_some_and(|t| t.holds_fresh(fresh))
            }
            Self::Spread(s) => s.elem.holds_fresh(fresh),
            Self::Handler(_) | Self::SelfTy | Self::Var(_) | Self::Value(_) | Self::Error => false,
        }
    }
}
