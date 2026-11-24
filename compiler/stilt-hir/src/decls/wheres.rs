//! The bounds of an impl's `where` clause on member types that a bound's argument fixes, which
//! the fixed type must meet as a bound beside a parameter is met (traits.where). A function's
//! are checked with its body, where its type's errors are reported.

use stilt_diag::codes;

use super::build::{Builder, Unit};
use super::implements::Answer;
use super::signatures::{Subst, bounds_of};
use crate::Anchor;
use crate::hir::{Generic, Item, Ty};

impl Builder {
    /// E0318 for each bound of an impl's `where` clause that the member type it bounds, fixed
    /// by a bound's argument, doesn't meet, at the member type, once per bound. It runs once
    /// every impl is known.
    pub(super) fn check_impl_wheres(&mut self, units: &[Unit<'_>]) {
        for unit in units {
            for (index, item) in (0..).zip(&unit.hir.items) {
                let crate::hir::ItemHir::Impl(block) = item else {
                    continue;
                };
                let bounds = bounds_of(&block.generics, &unit.owner(index, None));
                for (k, (ty, trait_item, args)) in (0..).zip(&block.fixed) {
                    if self.decls.implements(&bounds, ty, trait_item) != Answer::No
                        && self.gives_args(ty, trait_item, args)
                    {
                        continue;
                    }
                    let message = format!(
                        "`{}` doesn't implement `{}`, which this `where` clause asks of it",
                        shown(ty, &block.generics),
                        trait_item.name
                    );
                    self.problem(unit, Anchor::Where(index, k), codes::E0318, message);
                }
            }
        }
    }
}

impl Builder {
    /// Whether the impl of `trait_item` for `ty` gives it the arguments `args`, which a bound
    /// without arguments leaves open (traits.bound-arguments).
    fn gives_args(&self, ty: &Ty, trait_item: &Item, args: &[Ty]) -> bool {
        let Ty::Con(owner, targs) = ty else {
            return true;
        };
        let Some(imp) = self.decls.trait_impl(trait_item, owner) else {
            return true;
        };
        let Ty::Con(_, params) = &imp.self_ty else {
            return true;
        };
        let types = params
            .iter()
            .zip(targs)
            .filter_map(|(p, t)| match p {
                Ty::Param(v) => Some((v.clone(), t.clone())),
                _ => None,
            })
            .collect();
        let s = Subst {
            types,
            ..Subst::default()
        };
        let given: Vec<Ty> = imp.trait_args.iter().map(|a| s.ty(a)).collect();
        args.is_empty() || given.len() != args.len() || given == args
    }
}

/// A type as the program writes it, its type parameters named by `generics`.
fn shown(t: &Ty, generics: &[Generic]) -> String {
    let list = |ts: &[Ty]| {
        ts.iter()
            .map(|t| shown(t, generics))
            .collect::<Vec<_>>()
            .join(", ")
    };
    match t {
        Ty::Con(item, args) if item.is_record() => {
            let fields = item.record_fields();
            let fields: Vec<String> = fields
                .iter()
                .zip(args)
                .map(|(f, t)| format!("{f}: {}", shown(t, generics)))
                .collect();
            format!("{{ {} }}", fields.join(", "))
        }
        Ty::Con(item, args) if args.is_empty() => item.name.to_string(),
        Ty::Con(item, args) => format!("{}<{}>", item.name, list(args)),
        Ty::Param(p) => generics
            .get(p.index as usize)
            .map_or_else(|| "_".to_owned(), |g| g.name.to_string()),
        Ty::SelfTy => "Self".to_owned(),
        Ty::Value(v) => v.to_string(),
        Ty::App(head, args) => format!("{}<{}>", shown(head, generics), list(args)),
        Ty::Tuple(ts) if ts.len() == 1 => format!("({},)", list(ts)),
        Ty::Tuple(ts) => format!("({})", list(ts)),
        Ty::Fn(f) => {
            let params = f
                .params
                .iter()
                .map(|(_, t)| shown(t, generics))
                .collect::<Vec<_>>()
                .join(", ");
            let ret = f
                .ret
                .as_ref()
                .map_or_else(|| "()".to_owned(), |r| shown(r, generics));
            format!("fn({params}) -> {ret}")
        }
        Ty::Spread(_, t) => format!("..{}", shown(t, generics)),
        Ty::Handler(h) => {
            let effect = if h.effect.args.is_empty() {
                h.effect.effect.name.to_string()
            } else {
                format!("{}<{}>", h.effect.effect.name, list(&h.effect.args))
            };
            match &h.answer {
                Some(r) => format!("handler {effect} -> {}", shown(r, generics)),
                None => format!("handler {effect}"),
            }
        }
        Ty::Error => "_".to_owned(),
    }
}
