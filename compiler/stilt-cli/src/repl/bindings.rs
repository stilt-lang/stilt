//! The types of a session's bindings, and whether an edit changed them
//! (repl.bindings-across-edits).
//!
//! A binding keeps the declarations of the types its type names, and of the types that their
//! fields and payloads name in turn, as they were when it was bound: its value has the layout
//! that those declarations gave, so it keeps its meaning while they stay as they were. A
//! function type names no declaration, but a closure holds values of types that its type
//! doesn't name, so a binding whose type holds one changes with any declaration of a type or a
//! trait, the declarations that the layout of every value follows.

use std::collections::HashMap;

use stilt_db::{Database, Program};
use stilt_hir::decls::{TypeDefInfo, TypeInfo};
use stilt_hir::hir::{self, Item, Name};
use stilt_types::ty::Ty;

/// A binding of the session, as the database's side keeps it.
#[derive(Clone, Debug)]
pub(super) struct Binding {
    pub(super) id: u32,
    pub(super) name: Name,
    pub(super) ty: Ty,
    /// Its type as a program writes it, for notes.
    pub(super) shown: String,
    /// The declarations of the types its type names, in turn, as they were when it was bound.
    decls: Vec<(Item, Option<TypeInfo>)>,
    /// Whether its type holds a function type.
    holds_fn: bool,
}

impl Binding {
    pub(super) fn new(db: &Database, program: Program, id: u32, name: Name, ty: Ty) -> Self {
        let types = &stilt_hir::declarations(db, program).types;
        let mut named = Named {
            types,
            decls: Vec::new(),
            holds_fn: false,
        };
        named.ty(&ty);
        Self {
            id,
            name,
            shown: stilt_types::input::shown(db, program, &ty),
            ty,
            decls: named.decls,
            holds_fn: named.holds_fn,
        }
    }

    /// Whether the binding's type is as it was, in the program as it is now, whose types' and
    /// traits' declarations `moved` tells changed since the binding's last look.
    pub(super) fn unchanged(&self, db: &Database, program: Program, moved: bool) -> bool {
        if self.holds_fn && moved {
            return false;
        }
        let types = &stilt_hir::declarations(db, program).types;
        self.decls
            .iter()
            .all(|(item, info)| types.get(item) == info.as_ref())
    }

    /// The note that drops it.
    pub(super) fn note(&self) -> String {
        format!(
            "note: `{}` is dropped, since the edit changed its type, `{}`\n",
            self.name, self.shown
        )
    }
}

/// The declarations that a type names, in turn.
struct Named<'a> {
    types: &'a HashMap<Item, TypeInfo>,
    decls: Vec<(Item, Option<TypeInfo>)>,
    holds_fn: bool,
}

impl Named<'_> {
    fn ty(&mut self, ty: &Ty) {
        match ty {
            Ty::Con(item, args) => {
                self.item(item);
                for t in args {
                    self.ty(t);
                }
            }
            Ty::Tuple(ts) | Ty::App(_, ts) => ts.iter().for_each(|t| self.ty(t)),
            Ty::Spread(s) => self.ty(&s.elem),
            Ty::Fn(_) | Ty::Handler(_) => self.holds_fn = true,
            Ty::Param(_) | Ty::SelfTy | Ty::Var(_) | Ty::Value(_) | Ty::Error => {}
        }
    }

    fn hir(&mut self, ty: &hir::Ty) {
        match ty {
            hir::Ty::Con(item, args) => {
                self.item(item);
                for t in args {
                    self.hir(t);
                }
            }
            hir::Ty::Tuple(ts) | hir::Ty::App(_, ts) => ts.iter().for_each(|t| self.hir(t)),
            hir::Ty::Fn(_) | hir::Ty::Handler(_) => self.holds_fn = true,
            hir::Ty::Spread(_, t) => self.hir(t),
            hir::Ty::Param(_) | hir::Ty::SelfTy | hir::Ty::Value(_) | hir::Ty::Error => {}
        }
    }

    fn item(&mut self, item: &Item) {
        if self.decls.iter().any(|(i, _)| i == item) {
            return;
        }
        let info = self.types.get(item).cloned();
        self.decls.push((item.clone(), info.clone()));
        match info.map(|i| i.def) {
            Some(TypeDefInfo::Record(fields)) => fields.iter().for_each(|(_, t)| self.hir(t)),
            Some(TypeDefInfo::Variants(variants)) => {
                variants
                    .iter()
                    .flat_map(|(_, p)| p)
                    .for_each(|t| self.hir(t));
            }
            Some(TypeDefInfo::Builtin) | None => {}
        }
    }
}
