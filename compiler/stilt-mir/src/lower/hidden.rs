//! The hidden arguments of a call of a generic function: what stands for
//! each of its type parameters.

use stilt_hir::decls::Bounds;
use stilt_hir::hir::{GenericId, Item};
use stilt_types::ty::Ty;

use super::Lower;
use crate::mir::Arg;

impl Lower<'_> {
    /// The hidden arguments of a generic function: for each type parameter, its witness, then
    /// a dictionary for each of its bounds, but for a constructor parameter, whose constructor
    /// the callee's key gives.
    /// A pack's are those of each of its elements (`super::packs`), and a record-bounded
    /// parameter's the witnesses of its record type's arguments (`super::records`).
    pub(crate) fn generic_args(
        &mut self,
        params: &Bounds,
        packs: &[(GenericId, bool)],
        targs: &[Ty],
    ) -> Vec<Arg> {
        let mut hidden = Vec::new();
        let decls = self.decls();
        for ((g, traits), ty) in params.iter().zip(targs) {
            if let Some((_, dynamic)) = packs.iter().find(|(p, _)| p == g) {
                hidden.extend(self.pack_args(traits, ty, *dynamic));
            } else if super::records::has_record_bound(traits) {
                hidden.extend(self.record_args(ty).into_iter().map(Arg::Borrow));
            } else if !super::cons::is_constructor(&decls, traits) {
                hidden.extend(self.bound_witness(traits, ty));
                // A trait method's own type parameter that an impl or the default reads passes
                // its descriptor too, since a call through the trait can't see which reads it
                //.
                if self.carries(&Ty::Param(g.clone()), traits) {
                    hidden.push(Arg::Borrow(self.descriptor(ty)));
                }
            }
        }
        hidden
    }

    /// The witness of a type argument `ty`, and its dictionary for each of `traits`.
    pub(crate) fn bound_witness(&mut self, traits: &[Item], ty: &Ty) -> Vec<Arg> {
        let mut hidden = vec![Arg::Borrow(self.witness(ty))];
        for t in traits {
            hidden.push(Arg::Borrow(self.dict(ty, t)));
        }
        hidden
    }
}
