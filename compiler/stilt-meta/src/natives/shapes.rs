//! The accessors of `std.meta` (meta.shape-accessors, meta.fields and meta.variant-cases), all
//! native. Each takes the type arguments of its impl, the shape's type `T` first, and performs
//! nothing but the allocation of what it makes (meta.accessor-effects). A field or a case is its
//! position, and every other accessor is `()`.

use std::sync::Arc;

use stilt_hir::hir::Name;
use stilt_types::ty::Ty;

use super::Native;
use crate::eval::reflect::{Case, case_of};
use crate::eval::{Machine, R, int_kind, is_f32, ops_float};
use crate::value::{IntKind, MapValue, Value, prelude};

/// The natives of `Integer`, `Convert`, `Sized`, `Fields`, `Field`, `Cases` and `Case`.
pub(super) fn shapes<'a>(m: &mut Machine<'a>, n: &Native<'_>, values: &mut [Value<'a>]) -> R<'a> {
    let ty = n.targs.first().cloned().unwrap_or(Ty::Error);
    let arg = |i: usize| values.get(i).cloned().unwrap_or_else(Value::unit);
    let position = usize::try_from(arg(0).as_int()).unwrap_or(0);
    match (n.owner.unwrap_or(""), n.name) {
        ("Integer", "text") => Ok(Value::str(arg(1).as_int().to_string())),
        ("Integer", "parse") => Ok(Value::option(parsed(int_kind(&ty), arg(1).as_str()))),
        ("Convert", _) => convert(m, n.name, &ty, arg(1)),
        ("Sized", "get") => Ok(arg(1)),
        ("Sized", "make") => {
            let fits = i128::try_from(arg(1).as_list().len()).is_ok_and(|l| l == size(&ty));
            Ok(Value::option(fits.then(|| arg(1))))
        }
        ("Sized", "len") => Ok(Value::i64(size(&ty))),
        ("Fields", "len") => Ok(Value::i64(count(fields(m, &ty).len()))),
        ("Cases", "len") => Ok(Value::i64(count(cases(m, &ty).len()))),
        ("Fields", "build") => build(m, &ty, &arg(1)),
        ("Field", "name") => Ok(Value::str(&*fields(m, &ty)[position].0)),
        ("Field" | "Case", "index") => Ok(Value::i64(count(position))),
        ("Field", "get") => {
            let name = fields(m, &ty)[position].0;
            Ok(match arg(1) {
                Value::Tuple(xs) => xs.get().get(position).cloned().unwrap_or_else(Value::unit),
                v => v.field(&name).cloned().unwrap_or_else(Value::unit),
            })
        }
        ("Case", "name") => Ok(Value::str(&*cases(m, &ty)[position].0.name)),
        ("Case", "get") => {
            let item = cases(m, &ty)[position].0.clone();
            Ok(Value::option(match arg(1) {
                Value::Variant(x) if x.0 == item => Some(Value::tuple(x.1.to_vec())),
                _ => None,
            }))
        }
        ("Case", "make") => {
            let item = cases(m, &ty)[position].0.clone();
            let payload = match arg(1) {
                Value::Tuple(xs) => xs.to_vec(),
                _ => Vec::new(),
            };
            Ok(Value::variant(item, payload))
        }
        _ => unreachable!("the table names every accessor of `std.meta`: {}", n.name),
    }
}

fn count(n: usize) -> i128 {
    i128::try_from(n).unwrap_or(0)
}

/// meta.shape-accessors: the integer that `text` writes as `text` would write it, of the type's
/// range.
fn parsed<'a>(k: IntKind, text: &str) -> Option<Value<'a>> {
    let x: i128 = text.parse().ok()?;
    (k.holds(x) && x.to_string() == text).then_some(Value::Int(x, k))
}

/// generics.array-sizes: an array type's size, its second argument.
fn size(ty: &Ty) -> i128 {
    match ty {
        Ty::Con(_, args) => match args.get(1) {
            Some(Ty::Value(stilt_hir::hir::Value::Int(n))) => *n,
            _ => unreachable!("an array type's second argument is its size"),
        },
        _ => unreachable!("a `Sized<T, E>` is of an array type"),
    }
}

fn fields(m: &Machine<'_>, ty: &Ty) -> Vec<(Name, Ty)> {
    match case_of(m.image.decls, ty) {
        Case::Fields(_, fields) => fields,
        _ => unreachable!("a `Fields<T>` and a `Field<T, F>` are of a tuple or a record type"),
    }
}

fn cases(m: &Machine<'_>, ty: &Ty) -> Vec<(stilt_hir::hir::Item, Vec<Ty>)> {
    match case_of(m.image.decls, ty) {
        Case::Cases(cases) => cases,
        _ => unreachable!("a `Cases<T>` and a `Case<T, P>` are of a variant type"),
    }
}

/// meta.shape-accessors: a value as a value of the type `U`, and back: an `f32` exactly and rounded
/// back as numbers.conversions rounds, a set as its elements and a map as its entries, in insertion
/// order, kept by the element or key type's own `Eq` and `Hash`. A map made so has no default.
fn convert<'a>(m: &mut Machine<'a>, name: &str, ty: &Ty, v: Value<'a>) -> R<'a> {
    let case = case_of(m.image.decls, ty);
    let pairs = |map: &MapValue<'a>| {
        let entries = map.entries.get().iter();
        entries
            .map(|(k, v)| Value::tuple(vec![k.clone(), v.clone()]))
            .collect()
    };
    match (name, &case, v) {
        ("get", Case::Holds("Set", _), v) => match v.field("elements") {
            Some(Value::Map(map)) => Ok(Value::list(
                map.entries.get().iter().map(|(k, _)| k.clone()).collect(),
            )),
            _ => unreachable!("a set holds its elements in a map"),
        },
        ("get", Case::Holds("Map", _), Value::Map(map)) => Ok(Value::list(pairs(&map))),
        ("get", Case::Leaf("Float"), Value::Float(x, _)) => Ok(Value::Float(x, false)),
        ("make", Case::Leaf("Float"), Value::Float(x, _)) => Ok(ops_float(x, is_f32(ty))),
        ("make", Case::Holds("Set", _), v) => {
            let entries = v.as_list().iter().map(|x| (x.clone(), Value::unit()));
            let map = filled(m, entries.collect())?;
            Ok(Value::record(
                prelude("Set"),
                vec![(Name::from("elements"), map)],
            ))
        }
        ("make", Case::Holds("Map", _), v) => {
            let entries = v.as_list().iter().map(|x| match x {
                Value::Tuple(kv) if kv.len() == 2 => (kv[0].clone(), kv[1].clone()),
                _ => unreachable!("a map is made of pairs"),
            });
            filled(m, entries.collect())
        }
        (_, _, v) => Ok(v),
    }
}

/// A map of the entries, each inserted in turn by its key's `Eq`.
fn filled<'a>(m: &mut Machine<'a>, entries: Vec<(Value<'a>, Value<'a>)>) -> R<'a> {
    let mut kept: Vec<(Value<'a>, Value<'a>)> = Vec::with_capacity(entries.len());
    for (k, v) in entries {
        match m.find_key(&kept, &k)? {
            Some(i) => kept[i].1 = v,
            None => kept.push((k, v)),
        }
    }
    Ok(Value::Map(Arc::new(MapValue {
        entries: crate::value::Counted::new(kept),
        default: None,
    })))
}

/// meta.building: a value of a tuple or a record type made of the values `f` gives each field,
/// called once on each in order, at the field's type.
fn build<'a>(m: &mut Machine<'a>, ty: &Ty, f: &Value<'a>) -> R<'a> {
    let fields = fields(m, ty);
    let mut values = Vec::with_capacity(fields.len());
    for (i, (_, fty)) in fields.iter().enumerate() {
        let g = crate::eval::instantiate(f.clone(), vec![fty.clone()]);
        values.push(m.apply_value(&g, &mut vec![Value::i64(count(i))])?);
    }
    Ok(match ty {
        Ty::Tuple(_) => Value::tuple(values),
        Ty::Con(item, _) => {
            let named = fields.into_iter().map(|(n, _)| n).zip(values);
            Value::record(item.clone(), named.collect())
        }
        _ => unreachable!("`build` makes a tuple or a record"),
    })
}
