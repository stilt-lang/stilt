//! Which declared types can form a cycle (cycles.can-form-cycle): those with a field or a variant
//! whose type holds a `Shared<U>` that can reach itself, which `stilt show` prints. A type holds
//! itself, its fields' and its variants' types, its elements' and its arguments', and what they
//! hold; a `Shared<U>` can reach itself when `U` holds that same `Shared<U>`, a function type,
//! whose closure may capture any handle, or a type parameter, which may be any type.

use std::collections::HashSet;

use stilt_hir::decls::{Lookup, TypeDefInfo};
use stilt_hir::hir::{Item, Name};

use crate::ty::{Ty, instantiate};

/// The most types a walk looks at, past which it takes the type to hold any type: a type that
/// grows as it holds itself (tests.growth-test) holds infinitely many.
const MOST: usize = 4096;

/// The fields of a declared record, or the variants of a declared variant type, through which
/// its values can form a cycle, in declaration order.
#[must_use]
pub fn cycles(decls: &dyn Lookup, item: &Item) -> Vec<Name> {
    let Some(info) = decls.type_info(item) else {
        return Vec::new();
    };
    let own: Vec<Ty> = info.params.iter().cloned().map(Ty::Param).collect();
    let parts: Vec<(Name, Vec<Ty>)> = match &info.def {
        TypeDefInfo::Record(fields) => fields
            .iter()
            .map(|(f, t)| (*f, vec![instantiate(t, &info.params, &own)]))
            .collect(),
        TypeDefInfo::Variants(variants) => variants
            .iter()
            .map(|(v, ts)| {
                let ts = ts.iter().map(|t| instantiate(t, &info.params, &own));
                (*v, ts.collect())
            })
            .collect(),
        TypeDefInfo::Builtin => Vec::new(),
    };
    parts
        .into_iter()
        .filter(|(_, types)| types.iter().any(|t| holds_cycle(decls, t)))
        .map(|(name, _)| name)
        .collect()
}

/// Whether a type holds a `Shared<U>` that can reach itself.
fn holds_cycle(decls: &dyn Lookup, ty: &Ty) -> bool {
    held(decls, ty).types.iter().any(|t| {
        t.shared().is_some_and(|u| {
            let reached = held(decls, u);
            reached.any || reached.types.contains(t)
        })
    })
}

/// The types that a type holds, and whether it holds a function type or a type parameter,
/// which stand for any type.
struct Held {
    types: HashSet<Ty>,
    any: bool,
}

fn held(decls: &dyn Lookup, ty: &Ty) -> Held {
    let mut found = Held {
        types: HashSet::new(),
        any: false,
    };
    let mut pending = vec![ty.clone()];
    while let Some(ty) = pending.pop() {
        if found.types.len() > MOST {
            found.any = true;
            break;
        }
        if found.types.contains(&ty) {
            continue;
        }
        match parts(decls, &ty) {
            Some(parts) => pending.extend(parts),
            None => found.any = true,
        }
        found.types.insert(ty);
    }
    found
}

/// The types that a type holds directly, or `None` for a type that stands for any type: a
/// function type, a handler, a type parameter, `Self`, a constructor parameter applied, a pack,
/// and `Lazy<T>`, whose value is a function's until it is computed (polymorphism.lazy-values).
fn parts(decls: &dyn Lookup, ty: &Ty) -> Option<Vec<Ty>> {
    match ty {
        Ty::Con(item, args) => {
            let Some(info) = decls.type_info(item) else {
                return Some(args.clone());
            };
            let at = |t| instantiate(t, &info.params, args);
            Some(match &info.def {
                TypeDefInfo::Record(fields) => fields.iter().map(|(_, t)| at(t)).collect(),
                TypeDefInfo::Variants(vs) => {
                    vs.iter().flat_map(|(_, ts)| ts.iter().map(at)).collect()
                }
                TypeDefInfo::Builtin if &*item.home == "std.lazy" => return None,
                TypeDefInfo::Builtin => args.clone(),
            })
        }
        Ty::Tuple(types) => Some(types.clone()),
        Ty::Fn(_) | Ty::Handler(_) | Ty::Param(_) | Ty::SelfTy | Ty::App(..) | Ty::Spread(_) => {
            None
        }
        Ty::Var(_) | Ty::Value(_) | Ty::Error => Some(Vec::new()),
    }
}
