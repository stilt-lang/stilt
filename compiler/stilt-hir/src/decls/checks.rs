//! Records that contain themselves (declarations.recursive-types), and `main` (program.main).

use std::collections::{BTreeMap, BTreeSet};
use stilt_diag::codes;

use super::build::{Builder, Unit};
use super::implements::Answer;
use super::signatures::{equal, signature, unit_ty};
use super::{TypeDefInfo, TypeInfo, prelude_item};
use crate::Anchor;
use crate::hir::{DeclKind, GenericId, Item, ItemHir, Ty, TypeDef};

/// What a value of a record type can hold through record fields and tuple elements alone
/// (declarations.recursive-types).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Held {
    Record(Item),
    Param(GenericId),
}

impl Builder {
    /// declarations.recursive-types: a record that contains itself through records and tuples alone
    /// can't be constructed. What each record holds is found as a least fixed point, with the type
    /// parameters a record holds standing for the types they are instantiated with. Each group of
    /// records that hold one another is one error, at the last of them (errors.primary-spans).
    pub(super) fn check_record_cycles(&mut self, units: &[Unit<'_>]) {
        // Of two declarations with the same name, only the first is the type that names refer
        // to (errors.several-places).
        let mut records = Vec::new();
        for unit in units {
            let mut seen = BTreeSet::new();
            for (index, item) in (0..).zip(&unit.hir.items) {
                if let ItemHir::Decl(decl) = item
                    && let DeclKind::Type(t) = &decl.kind
                    && seen.insert(t.name)
                    && matches!(t.def, TypeDef::Record(_))
                {
                    records.push((unit.item(t.name), unit, index));
                }
            }
        }
        let holds = self.holds(records.iter().map(|(item, ..)| item));
        let holds_record = |a: &Item, b: &Item| {
            holds
                .get(a)
                .is_some_and(|h| h.contains(&Held::Record(b.clone())))
        };
        let mut cyclic: Vec<_> = records
            .iter()
            .filter(|(item, ..)| holds_record(item, item))
            .collect();
        while let Some(first) = cyclic.first().copied() {
            let (group, others): (Vec<_>, Vec<_>) = cyclic.into_iter().partition(|(other, ..)| {
                holds_record(&first.0, other) && holds_record(other, &first.0)
            });
            cyclic = others;
            if let Some((_, unit, index)) = group
                .into_iter()
                .max_by(|(_, a, i), (_, b, j)| (a.path, *i).cmp(&(b.path, *j)))
            {
                let message =
                    "this record contains itself, so no value of it can be built".to_owned();
                self.problem(unit, Anchor::Name(*index), codes::E0309, message);
            }
        }
    }

    /// What each of the `records` holds, as the least fixed point of what its fields hold.
    fn holds<'a>(&self, records: impl Iterator<Item = &'a Item>) -> BTreeMap<Item, BTreeSet<Held>> {
        let mut holds: BTreeMap<Item, BTreeSet<Held>> = records
            .map(|item| (item.clone(), BTreeSet::new()))
            .collect();
        loop {
            let next: BTreeMap<_, _> = holds
                .keys()
                .map(|item| {
                    let held = match self.decls.types.get(item) {
                        Some(TypeInfo {
                            def: TypeDefInfo::Record(fields),
                            ..
                        }) => fields
                            .iter()
                            .flat_map(|(_, t)| self.held(&holds, t))
                            .collect(),
                        _ => BTreeSet::new(),
                    };
                    (item.clone(), held)
                })
                .collect();
            if next == holds {
                return holds;
            }
            holds = next;
        }
    }

    /// What a value of type `t` holds through record fields and tuple elements alone.
    fn held(&self, holds: &BTreeMap<Item, BTreeSet<Held>>, t: &Ty) -> Vec<Held> {
        match t {
            Ty::Tuple(ts) => ts.iter().flat_map(|t| self.held(holds, t)).collect(),
            Ty::Spread(_, t) => self.held(holds, t),
            Ty::Param(p) => vec![Held::Param(p.clone())],
            // An anonymous record holds its fields' types, as a tuple does
            // (records.anonymous-types).
            Ty::Con(item, args) if item.is_record() => {
                args.iter().flat_map(|t| self.held(holds, t)).collect()
            }
            Ty::Con(item, args) => {
                let Some(TypeInfo {
                    params,
                    def: TypeDefInfo::Record(_),
                    ..
                }) = self.decls.types.get(item)
                else {
                    return Vec::new();
                };
                let Some(inside) = holds.get(item) else {
                    return Vec::new();
                };
                if params.len() != args.len() {
                    return Vec::new();
                }
                let mut held = vec![Held::Record(item.clone())];
                for h in inside {
                    match h {
                        Held::Record(r) => held.push(Held::Record(r.clone())),
                        Held::Param(id) => {
                            if let Some(i) = params.iter().position(|p| p == id) {
                                held.extend(self.held(holds, &args[i]));
                            }
                        }
                    }
                }
                held
            }
            Ty::SelfTy | Ty::App(..) | Ty::Fn(_) | Ty::Handler(_) | Ty::Value(_) | Ty::Error => {
                Vec::new()
            }
        }
    }

    /// program.main: `main` takes no parameters, returns `()` and performs at most `io` and a
    /// raise whose error can be shown.
    pub(super) fn check_main(&mut self, units: &[Unit<'_>]) {
        for unit in units {
            if &*unit.hir.name != "main" || unit.hir.std {
                continue;
            }
            for (index, item) in (0..).zip(&unit.hir.items) {
                let ItemHir::Decl(decl) = item else { continue };
                let DeclKind::Fn(f) = &decl.kind else {
                    continue;
                };
                if &*f.name != "main" {
                    continue;
                }
                let s = signature(f, &unit.owner(index, None), &Ty::Error, (&Vec::new(), &[]));
                let shows = s.row.raise.as_ref().is_none_or(|e| {
                    self.decls.implements(&Vec::new(), e, &prelude_item("Show")) != Answer::No
                });
                if !f.generics.is_empty()
                    || !f.params.is_empty()
                    || !equal(&s.ret, &unit_ty())
                    || s.row.var.is_some()
                    || !shows
                {
                    let message = "`main` must take no parameters, return `()` and perform at \
                                   most `io` and `raise<E>` with `E: Show`"
                        .to_owned();
                    self.problem(unit, Anchor::Name(index), codes::E0310, message);
                }
            }
        }
    }
}
