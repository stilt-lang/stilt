//! How an error comes back from a callee that raises in one word whatever its error's type
//! (effects.row-variables and effects.catch; goal inline-values): a closure's code, the code of a
//! function used as a value, and a function whose error is the one a function it is given raises,
//! through a row variable, written or implicit, and no `raise` label of its own.
//!
//! Such a callee takes, as its last argument, a pointer to memory for an error of several
//! words, which its caller provides, so that no error is ever boxed. A callee that raises an
//! error of one word returns it as any function returns its error; one that raises an error of
//! several words writes its words to that memory, and returns the raised flag. A caller that
//! knows the error's type, from the call's row, or from the `catch` or the signature that pairs the
//! row variable with it (effects.paired-row-variables; effects.passing-to-paired-variables),
//! provides memory for its words; one that doesn't, since the error comes through its own row
//! variable, passes on the memory that its own caller provided, and raises the error again as it
//! came.

use stilt_hir::decls::FnSig;
use stilt_types::ty::{Passing, Tail, Ty};

use super::calls::{Target, aborts};
use super::functions::signature;
use super::natives::Raised;
use super::{Conv, Form, Lower};
use crate::mir::{Arg, Operand, Terminator};

/// Whether a function of this signature raises in one word whatever its error's type: one
/// whose row has a row variable, written or implicit, or an effect whose handler may end a
/// `with` with an abort (`super::calls::aborts`), and no `raise` label; and a projection,
/// which raises what the caller's access raises (projections.raising-during-access).
pub(crate) fn raises_to_slot(sig: &FnSig) -> bool {
    let row = Passing::of(sig, None).row;
    sig.projection || (row.raise.is_none() && (!matches!(row.tail, Tail::Closed) || aborts(&row)))
}

impl Lower<'_> {
    /// Whether the code a target calls raises in one word, and so takes the memory for an error
    /// of several words as its last argument.
    pub(crate) fn target_raises_to_slot(&self, target: &Target) -> bool {
        match target {
            Target::Direct(f, _) => {
                signature(&self.decls(), f.generic()).is_some_and(|s| raises_to_slot(&s))
            }
            Target::Method(.., sig) => raises_to_slot(sig),
            Target::Crossing(c) => raises_to_slot(&c.sig),
        }
    }

    /// Passes a callee that raises in one word the memory for an error of several words, as its
    /// next argument, and tells how its error comes back when the call can raise: from the
    /// memory, or in the word it returns.
    pub(crate) fn slot_for_error(
        &mut self,
        args: &mut Vec<Arg>,
        err: &Conv,
        raises: bool,
    ) -> Option<Raised> {
        let known = if err.ty == Ty::Error {
            self.paired_error()
        } else {
            Some(err.ty.clone())
        };
        if raises
            && let Some(ty) = &known
            && !self.one_word(ty)
        {
            return Some(Raised::Slots(self.slots(args, ty)));
        }
        let slot = if raises && known.is_none() && self.raises_to_slot {
            Operand::Local(self.error_slot())
        } else {
            Operand::word(0)
        };
        args.push(Arg::Borrow(slot));
        raises.then(|| {
            Raised::Words(Conv {
                ty: known.unwrap_or(Ty::Error),
                form: Form::Word,
            })
        })
    }

    /// The type of an error that comes through a row variable: the one the nearest `catch`
    /// handles, or the function's own, which the signature pairs the variable with, if it is
    /// known.
    pub(crate) fn paired_error(&self) -> Option<Ty> {
        let ty = self.catchers.last().map_or(&self.err.ty, |c| &c.ty);
        (*ty != Ty::Error).then(|| ty.clone())
    }

    /// Ends the function with a raise of an error, whose words it consumes: an error of several
    /// words that the function raises in one word goes to the memory its caller provided.
    pub(crate) fn raise_out(&mut self, error: Vec<Operand>) {
        let err = self.err.clone();
        if self.raises_to_slot && err.ty != Ty::Error && !self.one_word(&err.ty) {
            let slot = Operand::Local(self.error_slot());
            self.store_words(&slot, error, &err.ty);
            self.b.terminate(Terminator::Raise(vec![Operand::word(0)]));
        } else {
            let words = self.passed(error, &err);
            self.b.terminate(Terminator::Raise(words));
        }
    }
}
