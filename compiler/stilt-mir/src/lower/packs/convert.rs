//! Calls from code that knows a pack's elements into code that takes its length at run time
//!: the call within a function's cycle that grows its pack, as polymorphic
//! recursion does. The callee holds a tuple of the pack as the list of its elements' boxes, so
//! the call converts each argument that is such a tuple into one, and a result that is one back.

use stilt_hir::hir::{self, GenericId, Mode};
use stilt_types::tast::{self, Callee as TCallee, Expr};
use stilt_types::ty::{Row, Ty};

use super::super::Lower;
use super::super::calls::{Target, can_raise};
use super::super::functions::signature;
use crate::FnRef;
use crate::mir::{Arg, Operand};

/// What a call converts: whether each parameter is a tuple of a pack the callee takes the length
/// of at run time, and whether the result is, as the callee holds it.
pub(crate) struct Conversions {
    params: Vec<bool>,
    ret: Option<Ty>,
}

/// Whether a declared type is a tuple that spreads one of `packs`, and whether it names one
/// of them anywhere else, which the call can't convert.
fn spreads(t: &hir::Ty, packs: &[GenericId]) -> (bool, bool) {
    let named = |t: &hir::Ty| names(t, packs);
    match t {
        hir::Ty::Tuple(ts) => {
            let top = ts
                .iter()
                .any(|t| matches!(t, hir::Ty::Spread(p, _) if packs.contains(p)));
            let deep = ts.iter().any(|t| match t {
                hir::Ty::Spread(_, elem) => named(elem),
                t => named(t),
            });
            (top, deep)
        }
        t => (false, named(t)),
    }
}

/// Whether a declared type names one of `packs`.
fn names(t: &hir::Ty, packs: &[GenericId]) -> bool {
    match t {
        hir::Ty::Param(p) => packs.contains(p),
        hir::Ty::Spread(p, elem) => packs.contains(p) || names(elem, packs),
        hir::Ty::Con(_, ts) | hir::Ty::Tuple(ts) => ts.iter().any(|t| names(t, packs)),
        hir::Ty::App(head, ts) => names(head, packs) || ts.iter().any(|t| names(t, packs)),
        hir::Ty::Fn(f) => {
            f.params.iter().any(|(_, t)| names(t, packs)) || f.ret.iter().any(|t| names(t, packs))
        }
        _ => false,
    }
}

impl Lower<'_> {
    /// What a call with the type arguments `targs` converts, if its callee takes the length of
    /// a pack at run time that this code knows.
    pub(crate) fn conversions(&mut self, callee: &TCallee, targs: &[Ty]) -> Option<Conversions> {
        let f = match callee {
            TCallee::Function(item) => FnRef::Function(item.clone()),
            TCallee::Member(owner, name) => FnRef::Member(owner.clone(), *name),
            TCallee::TraitMethod(..) | TCallee::Operation(..) => return None,
        };
        let sig = signature(&self.decls(), &f)?;
        let packs: Vec<GenericId> = self
            .pack_kinds(&sig, targs, Some(&f))
            .into_iter()
            .zip(&sig.type_params)
            .filter(|((_, dynamic), _)| *dynamic)
            .filter_map(|((g, _), _)| {
                let at = sig.type_params.iter().position(|(p, _)| *p == g)?;
                super::static_elements(targs.get(at)?).map(|_| g)
            })
            .collect();
        if packs.is_empty() {
            return None;
        }
        let mut params = Vec::new();
        for (mode, t) in &sig.params {
            let (top, deep) = spreads(t, &packs);
            if deep || top && *mode == Mode::Inout {
                self.b.met_error();
            }
            params.push(top);
        }
        let (top, deep) = spreads(&sig.ret, &packs);
        if deep {
            self.b.met_error();
        }
        let ret = top.then(|| Ty::from_hir(&sig.ret, None));
        Some(Conversions { params, ret })
    }

    /// A call that converts the tuples of packs its callee takes the length of at run time.
    pub(crate) fn converted_call(
        &mut self,
        target: Target,
        c: &Conversions,
        args: &[tast::Arg],
        row: &Row,
        e: &Expr,
    ) -> Vec<Operand> {
        let forms = self.forms_of(&target);
        let mut values = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let words = self.expr(&a.value);
            if c.params.get(i).copied().unwrap_or(false) {
                values.push(Arg::Borrow(self.pack_of_words(&words, &a.value.ty)));
            } else {
                values.extend(self.pass(words, &a.value.ty, forms.param(i)));
            }
        }
        let loc = self.loc_at(e.at);
        let ret = c.ret.clone().unwrap_or_else(|| e.ty.clone());
        let result = self.emit_call(target, values, &[], loc, can_raise(row), &ret, row);
        match c.ret {
            Some(_) => {
                let list = result.first().cloned().unwrap_or(Operand::word(0));
                self.words_of_pack(&list, &e.ty)
            }
            None => result,
        }
    }
}
