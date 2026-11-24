//! Which type arguments would grow a callee's instances without end, and the types that code
//! past the caps holds in their place (`super`).
//!
//! Within the instance's own cycle of the call graph, a type that it builds from its own type
//! parameters, with more words than a key holds ([`MAX_WORDS`]) and than any of its own keys,
//! crosses boxed, and so does any type that holds one, such as the
//! element type of a list, which keys the instances of the dictionaries made for it. The types
//! inside are replaced first, so that a type that crosses holds none that grows, and its
//! dictionaries, compiled for its own type arguments, have finitely many instances too: the
//! `(T, T)` of a `List<(T, T)>` crosses, and the list's type becomes a `List` of the generic
//! made up for it, whose dictionaries forward to those of `(T, T)`.

use stilt_types::ty::Ty;

use crate::Held;
use crate::lower::Lower;
use crate::lower::keys::MAX_WORDS;
use crate::mir::{Operand, Repr, Rvalue};

/// Whether a type names a type parameter.
fn names_param(ty: &Ty) -> bool {
    match ty {
        Ty::Param(_) | Ty::SelfTy => true,
        Ty::Tuple(ts) | Ty::Con(_, ts) => ts.iter().any(names_param),
        Ty::Fn(f) => {
            f.params.iter().any(|(_, t)| names_param(t))
                || names_param(&f.ret)
                || f.row.raise.as_deref().is_some_and(names_param)
        }
        _ => false,
    }
}

impl Lower<'_> {
    /// Whether a type is built from the type parameters in scope with more words than a key
    /// holds: more than [`MAX_WORDS`], and than any key of this function's own.
    fn too_big(&self, ty: &Ty) -> bool {
        matches!(ty, Ty::Tuple(_) | Ty::Con(..))
            && names_param(ty)
            && self.words_of(ty) > MAX_WORDS.max(self.widest_key())
    }

    /// Whether a type argument would grow its callee's instances: it, or a type it holds, is
    /// built from the type parameters in scope with more words than a key holds.
    pub(crate) fn grows(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Tuple(ts) | Ty::Con(_, ts) => self.too_big(ty) || ts.iter().any(|t| self.grows(t)),
            _ => false,
        }
    }

    /// A type as code past the caps holds it: each type inside it that grows its callee's
    /// instances replaced by a generic held in one word, from the innermost out.
    pub(crate) fn shrink(&mut self, ty: &Ty) -> Ty {
        let inner = match ty {
            Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| self.shrink(t)).collect()),
            Ty::Con(c, ts) => Ty::Con(c.clone(), ts.iter().map(|t| self.shrink(t)).collect()),
            _ => return ty.clone(),
        };
        if self.too_big(&inner) {
            self.crossing_for(inner)
        } else {
            inner
        }
    }

    /// A new generic, brought into scope, that stands for a value of type `ty` crossing in its
    /// box: held in one word, with `ty`'s witness, and dictionaries that forward to `ty`'s,
    /// made where they are needed ([`Lower::dict`]).
    pub(crate) fn crossing_for(&mut self, ty: Ty) -> Ty {
        let witness = match self.witness(&ty) {
            Operand::Local(l) => l,
            other @ Operand::Const(_) => self.b.define(Repr::Scalar, Rvalue::Use(other)),
        };
        let u = self.cross_generic();
        self.push_generic(u.clone(), witness, Vec::new(), Some(&Held::Word));
        self.crossing.push((u.clone(), ty));
        u
    }
}
