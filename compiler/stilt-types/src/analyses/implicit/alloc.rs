//! What allocates without a body to say so (facts.allocation and facts.native-allocation): a value
//! of a recursive type, a native function, and a method of an impl that no source declares, which
//! the type of its result decides.

use std::collections::HashSet;

use stilt_hir::decls::{FnSig, Lookup, TypeDefInfo};
use stilt_hir::hir::{self, Item, Mode};

use crate::ty::is_prelude;

/// The type constructors that a type names at any depth: its arguments', and a function
/// type's parameters', result's and raised error's.
fn named(t: &hir::Ty, out: &mut Vec<Item>) {
    match t {
        hir::Ty::Con(item, args) => {
            out.push(item.clone());
            for a in args {
                named(a, out);
            }
        }
        hir::Ty::Tuple(ts) => {
            for t in ts {
                named(t, out);
            }
        }
        hir::Ty::Spread(_, t) => named(t, out),
        hir::Ty::Fn(f) => {
            for (_, t) in &f.params {
                named(t, out);
            }
            for t in f.ret.iter().chain(f.row.raise.as_deref()) {
                named(t, out);
            }
        }
        hir::Ty::Handler(h) => {
            for t in h.effect.args.iter().chain(&h.answer) {
                named(t, out);
            }
        }
        hir::Ty::Param(_)
        | hir::Ty::SelfTy
        | hir::Ty::App(..)
        | hir::Ty::Value(_)
        | hir::Ty::Error => {}
    }
}

/// The types that the fields or payloads of a declared type name.
fn held(decls: &dyn Lookup, item: &Item) -> Vec<Item> {
    let mut out = Vec::new();
    match decls.type_info(item).map(|info| &info.def) {
        Some(TypeDefInfo::Record(fields)) => {
            for (_, t) in fields {
                named(t, &mut out);
            }
        }
        Some(TypeDefInfo::Variants(variants)) => {
            for t in variants.iter().flat_map(|(_, payload)| payload) {
                named(t, &mut out);
            }
        }
        Some(TypeDefInfo::Builtin) | None => {}
    }
    out
}

/// Whether a type is recursive: whether its declaration names it again, directly or through
/// the declarations of the types it names, type arguments included (facts.allocation). Its values
/// are the only ones of a declared type that live on the heap, so the compiler's layouts read it
/// too.
pub fn is_recursive(decls: &dyn Lookup, item: &Item) -> bool {
    let mut seen = HashSet::new();
    let mut next = held(decls, item);
    while let Some(t) = next.pop() {
        if t == *item {
            return true;
        }
        if seen.insert(t.clone()) {
            next.extend(held(decls, &t));
        }
    }
    false
}

/// Whether a type of a signature names `str`, `List` or `Map`, whose values live on the heap.
fn names_heap(t: &hir::Ty) -> bool {
    let mut items = Vec::new();
    named(t, &mut items);
    items
        .iter()
        .any(|i| is_prelude(i, "str") || is_prelude(i, "List") || is_prelude(i, "Map"))
}

/// Whether code with this signature and no body to read allocates: when its result names
/// `str`, `List` or `Map`, or one of its `inout` parameters does.
pub(super) fn signature_allocates(s: &FnSig) -> bool {
    names_heap(&s.ret)
        || s.params
            .iter()
            .any(|(mode, t)| *mode == Mode::Inout && names_heap(t))
}
