//! Reflection in a debug build: a function that names `T.shape`, `T.name`
//! or a bound test on `T`, or gives `T` to one that does, takes a descriptor of `T` after its
//! witnesses and dictionaries, and the accessors of `std.meta` compile inline, reading it. A
//! call gives it a value of `T` of several words in its box, past the caps (`super::bridge`), so
//! that it is compiled once for every type it is given for `T`, as it is for a fresh type. What
//! a call through a trait can't see travels beside a witness instead: the descriptor of a trait
//! method's own type parameter that an impl or the default reads, and of `Self` and a trait's
//! parameter that a default reads; and a dictionary holds those of its impl's type parameters.
//!
//! A descriptor is a data object: the number of its shape's case, its type's name, its witness,
//! its table of impls, four fields of its case ([`A`] to [`D`]), its type's identity and the
//! arguments its impls give the table's traits. The descriptors of its
//! parts are given by *thunks*, closures of no argument that make them when called, so that a
//! recursive type's descriptor is cyclic without holding itself. The table holds the
//! dictionary of each trait of [`stilt_types::reflects::tested_traits`], or 0, a structural
//! impl's being a shape dictionary of code that walks the descriptor ([`shaped`]). The values that
//! an accessor reads or makes it takes and gives in the one word that holds them where a type
//! parameter stands, which the code of a type parameter, and of a fresh type, holds.

mod access;
mod calls;
mod control;
mod describe;
mod impls;
mod name;
mod shaped;
#[cfg(test)]
mod tests;

pub(crate) use access::access;
pub(crate) use describe::describe;
pub(crate) use shaped::shaped;

use stilt_hir::decls::{FnSig, Lookup as _};
use stilt_hir::hir::{GenericId, Item, Value};
use stilt_types::reflects::{Carried, Key, carried, facts_of, tested_traits};
use stilt_types::ty::{Ty, meta_ty};

use super::{Conv, Lower};
use crate::FnRef;
use crate::described::{Described, numbered};
use crate::mir::{Arg, Callee, Const, Heapness, Operand, ParamMode, Repr};

/// The fields of a descriptor.
pub(crate) const KIND: u32 = 0;
pub(crate) const NAME: u32 = 1;
pub(crate) const WITNESS: u32 = 2;
pub(crate) const IMPLS: u32 = 3;
/// For `Int`, the kind of the integer; `Float`, 1 for `f64`; `Option`, `List`, `Set` and
/// `Array`, the element's thunk; `Map`, the key's; `Tuple`, `Record` and `Variants`, the number
/// of fields or variants.
pub(crate) const A: u32 = 4;
/// For `Map`, the value's thunk; `Array`, its size; `Tuple`, `Record` and `Variants`, the
/// entries of the fields or variants.
pub(crate) const B: u32 = 5;
/// For `Option` and `Array`, the closures that read its values and make them; for `Tuple` and
/// `Record`, the one that builds a value from a closure of each field's.
pub(crate) const C: u32 = 6;
pub(crate) const D: u32 = 7;
/// Its type's identity: its name with each type constructor's module, which two types share
/// only if they are the same.
pub(crate) const IDENT: u32 = 8;
/// For each trait of the table whose impl it has, the identities of the arguments the impl
/// gives the trait's parameters, joined by `;`, and otherwise "".
pub(crate) const IMPL_ARGS: u32 = 9;
pub(crate) const DESC_LEN: u32 = 10;

/// The fields of a field's entry, and of a variant's, which a `meta.Field` and a `meta.Case`
/// are: its name, its place, the thunk of its type, the witness of its type, and the closure
/// that reads it, then for a variant the one that makes it. A variant's type is the tuple of its
/// payload.
pub(crate) const E_NAME: u32 = 0;
pub(crate) const E_INDEX: u32 = 1;
pub(crate) const E_THUNK: u32 = 2;
pub(crate) const E_WITNESS: u32 = 3;
pub(crate) const E_GET: u32 = 4;
pub(crate) const E_MAKE: u32 = 5;
pub(crate) const FIELD_LEN: u32 = 5;
pub(crate) const CASE_LEN: u32 = 6;

/// The type of a descriptor, a word of `std.meta`'s, as the code that calls a thunk holds it.
pub(crate) fn desc_ty() -> Ty {
    meta_ty("Shape", vec![Ty::unit()])
}

/// The key of a function's facts of reflection, if its code takes descriptors of its own type
/// parameters: a function of a module or of an inherent impl. A trait impl's methods take
/// those of the impl's ([`Lower::impl_described`]).
fn key_of(f: &FnRef) -> Option<Key> {
    match f.generic() {
        FnRef::Function(item) => Some(Key::Function(item.clone())),
        FnRef::Member(owner, name) => Some(Key::Member(owner.clone(), *name)),
        _ => None,
    }
}

/// A type with its type parameters numbered, and the types they stand for, in order.
pub(crate) struct Template {
    pub(crate) described: Described,
    pub(crate) params: Vec<Ty>,
}

impl Lower<'_> {
    /// The type parameters of `f` whose descriptors it takes, in the order of its signature.
    pub(crate) fn described_params(&self, f: &FnRef, sig: &FnSig) -> Vec<GenericId> {
        if let FnRef::ImplMethod(t, owner, _) = f.generic() {
            return self.impl_described(t, owner);
        }
        let Some(key) = key_of(f) else {
            return Vec::new();
        };
        let facts = facts_of(self.cx.db, self.cx.program, key);
        sig.type_params
            .iter()
            .map(|(g, _)| g)
            .filter(|g| facts.iter().any(|f| f.param == **g))
            .cloned()
            .collect()
    }

    /// The type parameters of the impl of trait `t` for `owner` that its methods reflect on or
    /// name, and those that the type and the trait's arguments it gives hold, where the
    /// trait's defaults read `Self` or those parameters, in the order of its generics: its
    /// dictionary holds their descriptors, built where the bound is met
    /// (meta.unseen-instantiations), and each of its methods and entries takes them.
    pub(crate) fn impl_described(&self, t: &Item, owner: &Item) -> Vec<GenericId> {
        let decls = self.decls();
        let Some(info) = decls.trait_impl(t, owner) else {
            return Vec::new();
        };
        let facts: Vec<GenericId> = info
            .members
            .iter()
            .flat_map(|m| {
                let key = Key::ImplMethod(t.clone(), owner.clone(), m.name);
                facts_of(self.cx.db, self.cx.program, key).clone()
            })
            .map(|f| f.param)
            .collect();
        let carried = self.carried();
        let mut given = Vec::new();
        if carried.self_of(t) {
            given.push(Ty::from_hir(&info.self_ty, None));
        }
        let params = decls.trait_info(t).map(|i| i.params.clone());
        for (p, a) in params.unwrap_or_default().iter().zip(&info.trait_args) {
            if carried.generic(p) {
                given.push(Ty::from_hir(a, None));
            }
        }
        info.generics
            .iter()
            .map(|(g, _)| g)
            .filter(|g| {
                let one = std::slice::from_ref(*g);
                facts.contains(g) || given.iter().any(|a| crate::layout::names_param(a, one))
            })
            .cloned()
            .collect()
    }

    /// The type parameters whose descriptors travel with their witnesses, and the traits whose
    /// defaults take `Self`'s.
    pub(crate) fn carried(&self) -> &Carried {
        carried(self.cx.db, self.cx.program)
    }

    /// Whether the descriptor of a generic, bounded by `traits`, travels with its witness: a
    /// carried type parameter's, or in a trait's default method `Self`'s, where the trait's
    /// defaults read it.
    pub(crate) fn carries(&self, ty: &Ty, traits: &[Item]) -> bool {
        match ty {
            Ty::Param(g) => self.carried().generic(g),
            Ty::SelfTy => traits.iter().any(|t| self.carried().self_of(t)),
            _ => false,
        }
    }

    /// [`Lower::impl_described`] of a written impl; a structural impl's methods reflect on
    /// nothing.
    pub(crate) fn written_described(&self, imp: &crate::items::ImplRef) -> Vec<GenericId> {
        match imp {
            crate::items::ImplRef::Written { trait_item, owner } => {
                self.impl_described(trait_item, owner)
            }
            crate::items::ImplRef::Structural { .. } => Vec::new(),
        }
    }

    /// Whether each type argument of a call of `f` at `targs` crosses into it in its box: one
    /// whose descriptor `f` takes, but a pack's or a value's, held in several words, so that a
    /// function that reflects is compiled once for every type it is given, holding its values
    /// in one word, as the code that reflects holds a fresh type's.
    pub(crate) fn reflected_args(&self, f: &FnRef, sig: &FnSig, targs: &[Ty]) -> Vec<bool> {
        let described = self.described_params(f, sig);
        if described.is_empty() {
            return Vec::new();
        }
        let packs = sig.packs();
        sig.type_params
            .iter()
            .zip(targs)
            .map(|((g, _), a)| {
                described.contains(g)
                    && !packs.contains(g)
                    && !matches!(a, Ty::Value(_))
                    && !self.one_word(a)
            })
            .collect()
    }

    /// Adds a parameter for the descriptor of each type parameter whose descriptor `f` takes.
    pub(crate) fn add_descriptors(&mut self, f: &FnRef, sig: &FnSig) {
        for g in self.described_params(f, sig) {
            let d = self.b.param(Repr::Heap, ParamMode::Borrowed, None);
            self.set_descriptor(&Ty::Param(g), Operand::Local(d));
        }
    }

    /// The descriptors that a call of `f` at `targs` passes after its other hidden arguments.
    pub(crate) fn descriptor_args(&mut self, f: &FnRef, sig: &FnSig, targs: &[Ty]) -> Vec<Arg> {
        let params = self.described_params(f, sig);
        let given: Vec<Ty> = sig
            .type_params
            .iter()
            .zip(targs)
            .filter(|((g, _), _)| params.contains(g))
            .map(|(_, t)| t.clone())
            .collect();
        given
            .iter()
            .map(|t| Arg::Borrow(self.descriptor(t)))
            .collect()
    }

    /// Reads the descriptors of `params` from the fields of a data object `env` of `len` fields,
    /// from field `next` on, gives each parameter's generic its own, and gives them as hidden
    /// arguments.
    pub(crate) fn descriptors_from(
        &mut self,
        params: &[GenericId],
        (env, len): (crate::mir::Local, u32),
        next: &mut u32,
    ) -> Vec<Arg> {
        let mut out = Vec::new();
        for g in params {
            let desc = Operand::Local(self.borrowed_field(env, len, *next, Repr::Heap));
            *next += 1;
            self.set_descriptor(&Ty::Param(g.clone()), desc.clone());
            out.push(Arg::Borrow(desc));
        }
        out
    }

    /// Gives the generic of `ty` its descriptor.
    pub(crate) fn set_descriptor(&mut self, ty: &Ty, desc: Operand) {
        if let Some((_, g)) = self.generics.iter_mut().rev().find(|(t, _)| t == ty) {
            g.desc = Some(desc);
        }
    }

    /// Gives the generic last brought into scope its descriptor, if it has one.
    pub(crate) fn set_last_descriptor(&mut self, desc: Option<Operand>) {
        if let (Some(d), Some((_, g))) = (desc, self.generics.last_mut()) {
            g.desc = Some(d);
        }
    }

    /// The traits of a descriptor's table.
    pub(crate) fn table_traits(&self) -> Vec<Item> {
        tested_traits(self.cx.db, self.cx.program).clone()
    }

    /// The descriptor of a type, borrowed or new: a type parameter's own, or the one its thunk
    /// makes.
    pub(crate) fn descriptor(&mut self, ty: &Ty) -> Operand {
        if let Some(d) = self.generic(ty).and_then(|g| g.desc.clone()) {
            return d;
        }
        if let Some(n) = self.crossing_of(ty) {
            return self.descriptor(&n);
        }
        if matches!(ty, Ty::Param(_) | Ty::SelfTy) {
            return self.no_descriptor();
        }
        let thunk = self.thunk(ty);
        self.force(thunk)
    }

    /// The thunk of a type's descriptor: a closure of the code that describes its form, holding
    /// the witness and the descriptor of each type parameter it holds.
    pub(crate) fn thunk(&mut self, ty: &Ty) -> Operand {
        let t = self.template(ty);
        self.closure_of_form(FnRef::Describe(Box::new(t.described)), &t.params)
    }

    /// A closure of `code`, the code of a descriptor's form or of one of its accessors, holding
    /// the witness and the descriptor of each of `params`.
    pub(crate) fn closure_of_form(&mut self, code: FnRef, params: &[Ty]) -> Operand {
        let mut env = vec![(Operand::Const(Const::Code(code)), Heapness::Static(false))];
        for p in params {
            let w = self.witness(p);
            env.push((w, Heapness::Static(false)));
            let d = self.descriptor(p);
            env.push((d, Heapness::Static(true)));
        }
        self.alloc(0, env)
    }

    /// The descriptor that a thunk makes, new.
    pub(crate) fn force(&mut self, thunk: Operand) -> Operand {
        let loc = Operand::Local(self.loc);
        let ret = Conv::of(desc_ty());
        let err = Conv::boxed(Ty::Error);
        let words = self.finish_call(
            Callee::Value(thunk),
            Vec::new(),
            &[],
            loc,
            false,
            &ret,
            &err,
        );
        super::words::word(&words, 0)
    }

    /// A type with each type parameter it holds numbered, in the order they first appear.
    pub(crate) fn template(&self, ty: &Ty) -> Template {
        let mut params = Vec::new();
        let described = match ty {
            Ty::Con(..) | Ty::Tuple(_) | Ty::Value(_) | Ty::Param(_) | Ty::SelfTy => {
                self.form(ty, &mut params)
            }
            _ => {
                let pieces = self.pieces(ty, &mut params);
                Described::Other(pieces, self.constant_witness(ty))
            }
        };
        Template { described, params }
    }

    /// A type's form. A part that no form writes, as a function type, stands for itself as a
    /// type parameter, whose descriptor its own form's code makes.
    fn form(&self, ty: &Ty, params: &mut Vec<Ty>) -> Described {
        let list = |l: &Self, ts: &[Ty], params: &mut Vec<Ty>| -> Box<[Described]> {
            ts.iter().map(|t| l.form(t, params)).collect()
        };
        match ty {
            Ty::Con(item, args) => Described::Con(item.clone(), list(self, args, params)),
            Ty::Tuple(ts) if !super::packs::is_dynamic_tuple(ty) => {
                Described::Tuple(list(self, ts, params))
            }
            Ty::Value(v) => Described::Value(*v),
            // A value parameter that keys the instance has its value.
            Ty::Param(_) if let Some(n) = self.value_of(ty) => Described::Value(Value::Int(n)),
            _ => Described::Param(number(params, ty)),
        }
    }

    /// The witness of a type of one word, as a constant.
    fn constant_witness(&self, ty: &Ty) -> u64 {
        let heap = self.layout(ty).iter().all(|r| *r != Repr::Scalar);
        crate::shape::word(heap)
    }

    /// A type parameter without a descriptor, which only code with an error meets:
    /// meta.unseen-instantiations makes E0350 of what can't pass one. As for any error that
    /// lowering meets, the function panics in its place as code with an error does
    /// (program.programs-with-errors).
    fn no_descriptor(&mut self) -> Operand {
        self.b.met_error();
        Operand::word(0)
    }

    /// The generic of the type parameter that number `i` stands for in a descriptor's code.
    pub(crate) fn numbered_ty(i: u32) -> Ty {
        Ty::Param(numbered(i))
    }
}

/// The number of a type parameter among those found so far, added if it is new.
pub(crate) fn number(params: &mut Vec<Ty>, ty: &Ty) -> u32 {
    let i = params.iter().position(|p| p == ty).unwrap_or_else(|| {
        params.push(ty.clone());
        params.len() - 1
    });
    u32::try_from(i).expect("under 4G type parameters")
}
