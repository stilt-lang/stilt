//! Copy-on-write types (modes.copy-on-write-types): `str`, `List<T>`, `Map<K, V>`, a function type,
//! a recursive type (facts.allocation), or a record, tuple or variant type with a field, element or
//! payload of one. Only a binding of such a type has a point on the locality and uniqueness axes
//! other than the default, and only a list whose elements are of no such type is
//! written in place through an element's parts (facts.writes-in-place).

use std::cell::RefCell;
use std::collections::HashMap;

use crate::is_recursive;
use crate::ty::{Ty, instantiate, is_prelude};
use stilt_hir::decls::{Lookup, TypeDefInfo};
use stilt_hir::hir::{self, GenericId, Item, Mode};

/// Whether types are copy-on-write, each declared type with its arguments' answers decided
/// once.
pub struct Cow<'a> {
    decls: &'a dyn Lookup,
    known: RefCell<HashMap<(Item, Vec<bool>), bool>>,
}

impl std::fmt::Debug for Cow<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Cow").finish_non_exhaustive()
    }
}

impl<'a> Cow<'a> {
    /// The answers for the declarations of `decls`, none decided yet.
    pub fn new(decls: &'a dyn Lookup) -> Self {
        Self {
            decls,
            known: RefCell::default(),
        }
    }

    /// Whether a type is copy-on-write. A type parameter may stand for one, so it counts as
    /// one, as the facts are conservative (facts.without-alloc).
    pub fn ty(&self, t: &Ty) -> bool {
        match t {
            Ty::Con(item, args) => {
                let args: Vec<bool> = args.iter().map(|a| self.ty(a)).collect();
                self.con(item, &args)
            }
            Ty::Tuple(ts) => ts.iter().any(|t| self.ty(t)),
            Ty::Fn(_)
            | Ty::Handler(_)
            | Ty::Param(_)
            | Ty::SelfTy
            | Ty::App(..)
            | Ty::Spread(_) => true,
            Ty::Var(_) | Ty::Value(_) | Ty::Error => false,
        }
    }

    /// Whether a call may store an argument of type `from` in a value of one of `targets`, the
    /// types of its result and of its `inout` arguments (modes.call-stores): a part of one is a
    /// part of the other, or stands for any type, or the target's part is a function type, whose
    /// closures may capture anything.
    #[must_use]
    pub fn may_store(&self, from: &Ty, targets: &[Ty]) -> bool {
        let sources = self.parts(from);
        !sources.is_empty()
            && targets.iter().any(|target| {
                self.parts(target).iter().any(|q| {
                    matches!(q, Ty::Fn(_))
                        || stands_for_any(q)
                        || sources.iter().any(|p| p == q || stands_for_any(p))
                })
            })
    }

    /// The parts of a value of type `t`, each a copy-on-write type (modes.call-stores): the type
    /// itself, and the parts of what it holds, those of the values that a function's calls give
    /// back or write through its `inout` parameters included. A type met again adds nothing, and
    /// a recursive type's fields and payloads are walked the first time its declaration is met,
    /// so the walk ends, though a type may hold its own declaration at other arguments.
    fn parts(&self, t: &Ty) -> Vec<Ty> {
        let mut found = Vec::new();
        let mut expanded = Vec::new();
        self.walk_parts(t, &mut found, &mut expanded);
        found
    }

    fn walk_parts(&self, t: &Ty, found: &mut Vec<Ty>, expanded: &mut Vec<Item>) {
        if found.contains(t) || !self.ty(t) {
            return;
        }
        found.push(t.clone());
        let inner: Vec<Ty> = match t {
            Ty::Con(item, args) => self.held(item, args, expanded),
            Ty::Tuple(ts) => ts.clone(),
            Ty::Fn(f) => std::iter::once(f.ret.clone())
                .chain(
                    f.params
                        .iter()
                        .filter(|(mode, _)| *mode == Mode::Inout)
                        .map(|(_, t)| t.clone()),
                )
                .collect(),
            _ => Vec::new(),
        };
        for t in &inner {
            self.walk_parts(t, found, expanded);
        }
    }

    /// What a value of `item` applied to `args` holds: a built-in type's arguments, and a
    /// declared type's fields and payloads, or its arguments once its declaration, a recursive
    /// one, has been walked.
    fn held(&self, item: &Item, args: &[Ty], expanded: &mut Vec<Item>) -> Vec<Ty> {
        let Some(info) = self.decls.type_info(item) else {
            return Vec::new();
        };
        let written: Vec<&hir::Ty> = match &info.def {
            TypeDefInfo::Record(fields) => fields.iter().map(|(_, t)| t).collect(),
            TypeDefInfo::Variants(variants) => variants.iter().flat_map(|(_, p)| p).collect(),
            TypeDefInfo::Builtin => return args.to_vec(),
        };
        if expanded.contains(item) {
            return args.to_vec();
        }
        if is_recursive(self.decls, item) {
            expanded.push(item.clone());
        }
        written
            .iter()
            .map(|t| instantiate(t, &info.params, args))
            .collect()
    }

    /// Whether a type constructor applied to arguments, each copy-on-write or not, is.
    fn con(&self, item: &Item, args: &[bool]) -> bool {
        if ["str", "List", "Map"].iter().any(|n| is_prelude(item, n)) {
            return true;
        }
        // An array holds its elements inline, as a tuple does (generics.array-effects).
        if crate::ty::is_array(item) {
            return args.first().copied().unwrap_or(false);
        }
        let key = (item.clone(), args.to_vec());
        if let Some(&known) = self.known.borrow().get(&key) {
            return known;
        }
        let answer = match self.decls.type_info(item) {
            Some(info) => {
                let held: Vec<&hir::Ty> = match &info.def {
                    TypeDefInfo::Record(fields) => fields.iter().map(|(_, t)| t).collect(),
                    TypeDefInfo::Variants(variants) => {
                        variants.iter().flat_map(|(_, p)| p).collect()
                    }
                    TypeDefInfo::Builtin => Vec::new(),
                };
                !held.is_empty()
                    && (is_recursive(self.decls, item)
                        || held.iter().any(|t| self.declared(t, &info.params, args)))
            }
            None => false,
        };
        self.known.borrow_mut().insert(key, answer);
        answer
    }

    /// Whether a type that a declaration with the type parameters `params` writes is
    /// copy-on-write, where each parameter stands for an argument, copy-on-write or not.
    fn declared(&self, t: &hir::Ty, params: &[GenericId], args: &[bool]) -> bool {
        match t {
            hir::Ty::Con(item, targs) => {
                let targs: Vec<bool> = targs
                    .iter()
                    .map(|a| self.declared(a, params, args))
                    .collect();
                self.con(item, &targs)
            }
            hir::Ty::Param(g) => params
                .iter()
                .position(|p| p == g)
                .and_then(|i| args.get(i).copied())
                .unwrap_or(true),
            hir::Ty::Tuple(ts) => ts.iter().any(|t| self.declared(t, params, args)),
            hir::Ty::Fn(_)
            | hir::Ty::Handler(_)
            | hir::Ty::SelfTy
            | hir::Ty::App(..)
            | hir::Ty::Spread(..) => true,
            hir::Ty::Value(_) | hir::Ty::Error => false,
        }
    }
}

/// Whether a type may stand for any type, so that a part of it may be a part of anything
/// (modes.call-stores).
fn stands_for_any(t: &Ty) -> bool {
    matches!(
        t,
        Ty::Param(_) | Ty::SelfTy | Ty::App(..) | Ty::Spread(_) | Ty::Handler(_)
    )
}
