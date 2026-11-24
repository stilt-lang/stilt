//! The promise of an in-place `inout` parameter (facts.in-place-promise): a call makes the storage
//! of the place it gives such a parameter unique, where it reads the place, so the callee's writes
//! copy nothing. A caller whose place no other value shares makes it unique at no cost; one whose
//! place is shared copies it here, in its own code, as the copy at the call that facts.copy-at-call
//! counts. `stilt-rc` does the same for an in-place `let` parameter, once its counting has given
//! the call its reference.

use stilt_types::promises::in_place_params;

use super::Lower;
use crate::FnRef;
use crate::key_of;
use crate::mir::{Operand, Runtime, Stmt};

impl Lower<'_> {
    /// Whether each parameter of `f`, by its place among the source's, is in place
    /// (facts.in-place-parameters).
    pub(crate) fn in_place(&self, f: &FnRef) -> Vec<bool> {
        let Some(key) = key_of(f) else {
            return Vec::new();
        };
        let Some(params) = in_place_params(self.cx.db, self.cx.program).get(&key) else {
            return Vec::new();
        };
        let n = params.iter().max().map_or(0, |m| m + 1);
        (0..n).map(|i| params.contains(&i)).collect()
    }

    /// Makes unique the storage of the list in the slot that `slot` points to.
    pub(crate) fn unique_slot(&mut self, slot: &Operand) {
        self.b
            .emit(Stmt::Effect(Runtime::Unique, vec![slot.clone()]));
    }
}
