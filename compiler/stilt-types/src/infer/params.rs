//! The arguments of traits with parameters in a body (traits.trait-arguments,
//! traits.bound-arguments, traits.member-types and traits.constructor-parameters): those a
//! receiver's impl or bound gives a trait's method, and those a bound asks of the type that
//! instantiates it, decided as soon as that type is known.

use stilt_diag::codes;
use stilt_hir::hir::{GenericId, Item};
use stilt_syntax::TextRange;

use super::State;
use crate::params::{Args, TraitArgs, trait_subst};
use crate::ty::Ty;

impl State<'_> {
    pub(super) fn args(&self) -> Args<'_> {
        Args {
            decls: self.env.decls,
            scope: &self.env.bound_args,
            table: &self.table,
        }
    }

    /// The arity of a trait's `Self`: 0 for a trait over types (traits.constructor-traits).
    pub(super) fn arity(&self, trait_item: &Item) -> u32 {
        self.env.decls.trait_info(trait_item).map_or(0, |i| i.arity)
    }

    /// What `Self` is in a method of `trait_item` called on `receiver`: the receiver's type, or for
    /// a constructor trait the constructor at its head (traits.constructor-traits and
    /// traits.constructor-parameters), a variable when it isn't known yet.
    pub(super) fn self_for(&mut self, trait_item: &Item, receiver: &Ty, at: TextRange) -> Ty {
        if self.arity(trait_item) == 0 {
            return receiver.clone();
        }
        match self.table.shape(receiver) {
            Ty::Con(item, _) => Ty::Con(item, Vec::new()),
            Ty::App(head, _) => *head,
            Ty::Error => Ty::Error,
            _ => self.fresh(at),
        }
    }

    /// The type that must implement `trait_item` for its method to be called on `receiver`:
    /// the receiver's type, or for a constructor trait the constructor `self_ty` at its head
    /// (traits.constructor-parameters).
    pub(super) fn implementer<'t>(
        &self,
        trait_item: &Item,
        receiver: &'t Ty,
        self_ty: &'t Ty,
    ) -> &'t Ty {
        if self.arity(trait_item) > 0 {
            self_ty
        } else {
            receiver
        }
    }

    /// The types that a trait's parameters stand for in a method called on `receiver`: those
    /// its impl or bound gives, or variables that an obligation decides once its type is known
    /// (traits.trait-arguments and traits.member-types).
    pub(super) fn trait_params(
        &mut self,
        trait_item: &Item,
        receiver: &Ty,
        at: TextRange,
    ) -> Vec<(GenericId, Ty)> {
        let n = self
            .env
            .decls
            .trait_info(trait_item)
            .map_or(0, |i| i.params.len());
        if n == 0 {
            return Vec::new();
        }
        let args = match self.args().of(receiver, trait_item) {
            TraitArgs::Known(args) => args,
            TraitArgs::Missing => vec![Ty::Error; n],
            TraitArgs::Unknown => {
                let vars: Vec<Ty> = (0..n).map(|_| self.fresh(at)).collect();
                let wanted = (receiver.clone(), trait_item.clone(), vars.clone(), at);
                self.arg_obligations.push(wanted);
                vars
            }
        };
        trait_subst(self.env.decls, trait_item, &args)
    }

    /// Decides the obligations whose types are known: each type's impl or bound gives its
    /// trait's parameters the bound's arguments, or the use is E0318 (traits.bound-arguments).
    pub(super) fn settle_args(&mut self) {
        loop {
            let pending = std::mem::take(&mut self.arg_obligations);
            let before = pending.len();
            for (ty, t, wanted, at) in pending {
                match self.args().of(&ty, &t) {
                    TraitArgs::Unknown => self.arg_obligations.push((ty, t, wanted, at)),
                    TraitArgs::Missing if t.is_record_bound() => {
                        self.record_missing(&ty, &t, &wanted, at);
                    }
                    // The type's missing impl is the trait's own obligation.
                    TraitArgs::Missing => {}
                    TraitArgs::Known(actual) if t.is_record_bound() => {
                        self.meet_record(&ty, &t, (&wanted, &actual), at);
                    }
                    TraitArgs::Known(actual) => self.meet_args(&ty, &t, &wanted, &actual, at),
                }
            }
            if self.arg_obligations.len() == before {
                break;
            }
        }
    }

    /// E0318 unless the arguments a type's impl gives its trait are those a bound wants.
    fn meet_args(&mut self, ty: &Ty, t: &Item, wanted: &[Ty], actual: &[Ty], at: TextRange) {
        let differs = wanted
            .iter()
            .zip(actual)
            .any(|(w, a)| !self.table.unify(w, a));
        if differs {
            let message = format!(
                "`{}` implements `{}<{}>`, but the bound needs `{}<{}>`",
                self.show(ty),
                t.name,
                self.list(actual),
                t.name,
                self.list(wanted),
            );
            self.error(codes::E0318, at, message);
        }
    }

    fn list(&self, ts: &[Ty]) -> String {
        ts.iter()
            .map(|t| self.show(t))
            .collect::<Vec<_>>()
            .join(", ")
    }
}
