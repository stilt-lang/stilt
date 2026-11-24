//! Reflection at run time (meta.reflects), as the reference interpreter runs it: the shapes and the
//! names of the concrete types that a frame's type arguments give, bound tests (meta.bound-tests),
//! value parameters (generics.value-parameters-in-body), and the fresh types that a shape's arm and
//! a loop over fields or cases bind (meta.fresh-types, meta.fields and meta.variant-cases). A
//! shape's accessors are tokens that their types describe: a field or a case is its position, and
//! every other accessor is `()`.

use stilt_hir::decls::{Lookup, TypeDefInfo};
use stilt_hir::hir::{self, GenericId, Item, Name};
use stilt_types::tast::Reflection;
use stilt_types::ty::{Table, Ty, case_payload, is_meta, meta_item, meta_ty};

use super::calls::matching;
use super::{Frame, Machine, int_kind, substituted};
use crate::value::Value;

/// The case of a type's shape that fits it first (meta.shapes), with the types it holds.
#[derive(Debug)]
pub(crate) enum Case {
    Leaf(&'static str),
    Holds(&'static str, Vec<Ty>),
    Fields(&'static str, Vec<(Name, Ty)>),
    Cases(Vec<(Item, Vec<Ty>)>),
}

impl Case {
    fn name(&self) -> &'static str {
        match self {
            Case::Leaf(n) | Case::Holds(n, _) | Case::Fields(n, _) => n,
            Case::Cases(_) => "Variants",
        }
    }
}

/// The type `t` of a declaration of `info`'s, with `args` for its type parameters.
fn declared_ty(params: &[GenericId], args: &[Ty], t: &hir::Ty) -> Ty {
    let tenv: Vec<(GenericId, Ty)> = params.iter().cloned().zip(args.iter().cloned()).collect();
    substituted(&tenv, &Ty::from_hir(t, None))
}

/// A declared record, in the order of its declaration, or a declared variant type, but for
/// `Shape`, a native type, which has none (meta.types-without-shape).
fn declared(decls: &dyn Lookup, item: &Item, args: &[Ty]) -> Option<Case> {
    let info = decls.type_info(item)?;
    match &info.def {
        TypeDefInfo::Record(fields) => Some(Case::Fields(
            "Record",
            fields
                .iter()
                .map(|(n, t)| (*n, declared_ty(&info.params, args, t)))
                .collect(),
        )),
        TypeDefInfo::Variants(vs) if !is_meta(item, "Shape") => Some(Case::Cases(
            vs.iter()
                .map(|(n, payload)| {
                    let case = Item {
                        home: item.home,
                        name: *n,
                    };
                    let payload = payload.iter().map(|t| declared_ty(&info.params, args, t));
                    (case, payload.collect())
                })
                .collect(),
        )),
        _ => None,
    }
}

/// The case of the shape of a concrete type.
pub(crate) fn case_of(decls: &dyn Lookup, ty: &Ty) -> Case {
    let found = match ty {
        Ty::Con(item, args) if &*item.home == "std.prelude" => match (&*item.name, &args[..]) {
            ("i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64", []) => {
                Some(Case::Leaf("Int"))
            }
            ("f32" | "f64", []) => Some(Case::Leaf("Float")),
            ("bool", []) => Some(Case::Leaf("Bool")),
            ("str", []) => Some(Case::Leaf("Str")),
            ("Option", [_]) => Some(Case::Holds("Option", args.clone())),
            ("List", [_]) => Some(Case::Holds("List", args.clone())),
            ("Set", [_]) => Some(Case::Holds("Set", args.clone())),
            ("Map", [_, _]) => Some(Case::Holds("Map", args.clone())),
            _ => declared(decls, item, args),
        },
        Ty::Con(item, args) if &*item.home == "std.array" && &*item.name == "Array" => {
            Some(Case::Holds("Array", args.iter().take(1).cloned().collect()))
        }
        Ty::Con(item, args) if item.is_record() => {
            // records.field-order: in the order of their names, which the item keeps.
            let fields = item.record_fields().into_iter().zip(args.iter().cloned());
            Some(Case::Fields("Record", fields.collect()))
        }
        Ty::Con(item, args) => declared(decls, item, args),
        Ty::Tuple(ts) if ts.is_empty() => Some(Case::Leaf("Unit")),
        Ty::Tuple(ts) => Some(Case::Fields(
            "Tuple",
            ts.iter()
                .enumerate()
                .map(|(i, t)| (Name::from(i.to_string().as_str()), t.clone()))
                .collect(),
        )),
        _ => None,
    };
    found.unwrap_or_else(|| unreachable!("a reflected type has a shape, as checking found: {ty:?}"))
}

/// A type's name, as a diagnostic writes it (meta.shape-and-name).
pub(crate) fn describe(ty: &Ty) -> String {
    let names = |g: &GenericId| Name::from(g.fresh_letter().unwrap_or('T').to_string().as_str());
    Table::default().show(ty, &names)
}

/// The value of a value parameter in scope, of type `ty` (generics.value-parameters-in-body).
pub(crate) fn value_param<'a>(fr: &Frame<'a>, g: &GenericId, ty: &Ty) -> Value<'a> {
    match substituted(&fr.info.tenv, &Ty::Param(g.clone())) {
        Ty::Value(hir::Value::Int(n)) => Value::Int(n, int_kind(ty)),
        Ty::Value(hir::Value::Bool(b)) => Value::Bool(b),
        other => unreachable!("a value parameter is given a value when its body runs: {other:?}"),
    }
}

/// The type parameters that a type holds.
fn params_of(ty: &Ty, out: &mut Vec<GenericId>) {
    match ty {
        Ty::Param(g) => out.push(g.clone()),
        Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().for_each(|t| params_of(t, out)),
        _ => {}
    }
}

/// meta.fresh-types: binds the fresh types that the pattern type `pty` holds to the parts of
/// `concrete` they stand for, in the frame's type arguments.
pub(crate) fn bind_fresh(fr: &mut Frame<'_>, pty: &Ty, concrete: &Ty) {
    let mut held = Vec::new();
    params_of(pty, &mut held);
    held.retain(GenericId::is_fresh);
    if held.is_empty() {
        return;
    }
    let others: Vec<(GenericId, Ty)> = fr
        .info
        .tenv
        .iter()
        .filter(|(g, _)| !held.contains(g))
        .cloned()
        .collect();
    let mut bound = Vec::new();
    matching(&substituted(&others, pty), concrete, &mut bound);
    bound.retain(|(g, _)| held.contains(g));
    fr.bind_types(bound);
}

impl<'a> Machine<'a> {
    /// `T.shape()` or `T.name()` of the concrete type that `ty` is in the frame.
    pub(super) fn reflect(&self, fr: &Frame<'a>, what: Reflection, ty: &Ty) -> Value<'a> {
        let ty = substituted(&fr.info.tenv, ty);
        match what {
            Reflection::Shape => {
                let case = case_of(self.image.decls, &ty);
                Value::variant(meta_item(case.name()), vec![Value::unit()])
            }
            Reflection::Name => Value::str(describe(&ty)),
        }
    }

    /// meta.bound-tests: whether the concrete type has an impl of each bound, with its arguments,
    /// whose own bounds hold.
    pub(super) fn bound_holds(&self, fr: &Frame<'a>, ty: &Ty, traits: &[(Item, Vec<Ty>)]) -> bool {
        let ty = substituted(&fr.info.tenv, ty);
        let decls = self.image.decls;
        traits.iter().all(|(t, args)| {
            let none = Vec::new();
            stilt_types::implements_trait(decls, (&none, &[]), &ty, t)
                && (args.is_empty() || {
                    let args: Vec<Ty> =
                        args.iter().map(|a| substituted(&fr.info.tenv, a)).collect();
                    trait_args(decls, &ty, t).is_some_and(|given| given == args)
                })
        })
    }

    /// The types of the fields of a `meta.Fields<T>`, or of the cases of a `meta.Cases<T>`,
    /// as a loop over them binds each (meta.fields and meta.variant-cases).
    pub(super) fn reflected_elements(&self, fr: &Frame<'a>, ty: &Ty) -> Option<Vec<Ty>> {
        let Ty::Con(item, args) = substituted(&fr.info.tenv, ty) else {
            return None;
        };
        let of = args.first()?;
        let decls = self.image.decls;
        if is_meta(&item, "Fields") {
            let Case::Fields(_, fields) = case_of(decls, of) else {
                unreachable!("a `Fields<T>` is of a tuple or a record type")
            };
            let field = |(_, f): (Name, Ty)| meta_ty("Field", vec![of.clone(), f]);
            return Some(fields.into_iter().map(field).collect());
        }
        if is_meta(&item, "Cases") {
            let Case::Cases(cases) = case_of(decls, of) else {
                unreachable!("a `Cases<T>` is of a variant type")
            };
            let case = |(_, p): (Item, Vec<Ty>)| meta_ty("Case", vec![of.clone(), Ty::Tuple(p)]);
            return Some(cases.into_iter().map(case).collect());
        }
        None
    }

    /// The pattern of a case of `Shape<T>`, of type `shape`, binds its payload's fresh types to
    /// the types that `T` holds (meta.fresh-types).
    pub(crate) fn bind_case(&self, fr: &mut Frame<'a>, shape: &Ty, case: &str, payload: &Ty) {
        let Ty::Con(_, args) = substituted(&fr.info.tenv, shape) else {
            return;
        };
        let Some(t) = args.first() else {
            return;
        };
        let held = match case_of(self.image.decls, t) {
            Case::Holds(_, held) => held,
            _ => Vec::new(),
        };
        let mut fresh = |letter: char| {
            let i = usize::from(letter == 'V');
            held.get(i).cloned().unwrap_or(Ty::Error)
        };
        if let Some(concrete) = case_payload(case, t, &mut fresh) {
            bind_fresh(fr, payload, &concrete);
        }
    }
}

/// The arguments that the impl of `t` for the concrete type `ty` gives the trait's parameters.
fn trait_args(decls: &dyn Lookup, ty: &Ty, t: &Item) -> Option<Vec<Ty>> {
    let Ty::Con(owner, _) = ty else {
        return None;
    };
    let info = decls.trait_impl(t, owner)?;
    let mut bound = Vec::new();
    matching(&Ty::from_hir(&info.self_ty, None), ty, &mut bound);
    let args = info
        .trait_args
        .iter()
        .map(|a| substituted(&bound, &Ty::from_hir(a, None)));
    Some(args.collect())
}
