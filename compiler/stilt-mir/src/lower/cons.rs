//! Constructor parameters (traits.constructor-parameters). A function with a constructor parameter,
//! and a constructor trait's default method, are compiled for the constructor that each call
//! gives them, which the instance's key names ([`crate::Held::Con`]): its typed code is
//! retyped with every type that applies the parameter that constructor applied, so the code
//! calls the constructor's impls directly and holds their values in their own layouts, and
//! no witness or dictionary stands for the parameter.

use stilt_hir::decls::Lookup;
use stilt_hir::hir::{GenericId, Item};
use stilt_types::tast::Code;
use stilt_types::tast::retype::Retype;
use stilt_types::ty::{Row, Subst, Table, Ty};

use super::Lower;
use crate::Held;

/// The constructors an instance's key gives its constructor parameters.
#[derive(Clone, Debug, Default)]
pub(crate) struct Cons {
    /// Each constructor parameter, with its constructor, a type constructor written without
    /// its arguments.
    pub(crate) params: Vec<(GenericId, Ty)>,
    /// `Self` in a constructor trait's default method.
    pub(crate) self_ty: Option<Ty>,
    /// The number of the key's generics they take.
    pub(crate) taken: usize,
    /// The number of generics in scope that the key doesn't give: the elements of packs and
    /// the arguments of record types, which a key's one generic holds (`super::packs`,
    /// `super::records`).
    pub(crate) extra: usize,
}

impl Cons {
    pub(crate) fn is_empty(&self) -> bool {
        self.params.is_empty() && self.self_ty.is_none()
    }

    fn subst(&self) -> Subst {
        Subst {
            self_ty: self.self_ty.clone(),
            types: self.params.clone(),
            rows: Vec::new(),
        }
    }

    /// A type of the instance's code, each constructor parameter its constructor.
    pub(crate) fn ty(&self, t: &Ty) -> Ty {
        if self.is_empty() {
            return t.clone();
        }
        Table::default().subst(&self.subst(), t)
    }

    /// A row of the instance's code, its raise's type retyped.
    pub(crate) fn row(&self, r: &Row) -> Row {
        if self.is_empty() {
            return r.clone();
        }
        Table::default().subst_row(&self.subst(), r)
    }
}

/// Whether a type parameter with the bounds `traits` is a constructor parameter: one that a
/// constructor trait bounds (traits.constructor-parameters).
pub(crate) fn is_constructor(decls: &dyn Lookup, traits: &[Item]) -> bool {
    traits
        .iter()
        .any(|t| decls.trait_info(t).is_some_and(|info| info.arity > 0))
}

/// The key of a constructor parameter instantiated with `ty`: the constructor at its head.
pub(crate) fn con_key(ty: &Ty) -> Held {
    match ty {
        Ty::Con(item, _) => Held::Con(item.clone()),
        _ => Held::Word,
    }
}

impl Lower<'_> {
    /// Takes the next generic of the instance's key as a constructor parameter's, and gives its
    /// constructor, or the error type for a key that names none.
    pub(crate) fn take_con(&mut self) -> Ty {
        let index = self.key_index();
        self.cons.taken += 1;
        match self.held.get(index) {
            Some(Held::Con(item)) => Ty::Con(item.clone(), Vec::new()),
            _ => Ty::Error,
        }
    }

    /// The place in the instance's key of the next generic it gives.
    pub(crate) fn key_index(&self) -> usize {
        self.generics.len() + self.cons.taken - self.cons.extra
    }

    /// The typed code of the function, retyped for the constructors of its key. The bodies of
    /// spreads are retyped for each element where they are lowered (`super::packs`).
    pub(crate) fn retyped(&self, code: &Code) -> Code {
        let mut code = code.clone();
        if !self.cons.is_empty() {
            let ty = |t: &Ty| self.cons.ty(t);
            let row = |r: &Row| self.cons.row(r);
            Retype {
                ty: &ty,
                row: &row,
                spreads: false,
            }
            .code(&mut code);
        }
        code
    }
}
