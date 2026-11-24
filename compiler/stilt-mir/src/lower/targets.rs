//! What a call of a trait's method calls (traits.method-resolution and traits.structural-impls):
//! the method of the impl that the receiver's constructor has, written or structural, or, on a type
//! parameter, the method of its dictionary, unless the instance knows the parameter's constructor
//! ([`crate::Known`]), whose impl's method it then calls directly.

use stilt_hir::decls::{Bounds, FnSig, ImplInfo, Lookup};
use stilt_hir::hir::{self, Item, Name};
use stilt_types::ty::Ty;

use super::Lower;
use super::bridge::{Crossing, Past};
use super::calls::Target;
use super::functions::{calls_own, trait_method};
use super::keys::keyed;
use crate::items::{ImplRef, Shape};
use crate::mir::{Arg, Operand, Repr, Rvalue};
use crate::{FnRef, Held};

impl Lower<'_> {
    /// A method of a trait, on a receiver of type `ty`: through the dictionary of a type
    /// parameter, or of the impl that the receiver's constructor has, written or structural
    /// (traits.method-resolution and traits.structural-impls).
    pub(crate) fn trait_target(&mut self, t: &Item, name: Name, ty: &Ty, own: &[Ty]) -> Target {
        let Some((index, msig)) = trait_method(&self.decls(), t, name) else {
            return Target::Direct(FnRef::Main, Vec::new());
        };
        let param = matches!(ty, Ty::Param(_) | Ty::SelfTy);
        let known = param && self.generic(ty).is_some_and(|g| g.known.is_some());
        // A receiver or a type argument that would grow the instances without end, within this
        // function's cycle, calls past the caps. A projection's access would cross with it,
        // which the bridge doesn't convert: its instances follow its type arguments.
        if (!param || known)
            && !msig.projection
            && (self.grows(ty) || own.iter().any(|o| self.grows(o)))
            && self.trait_in_cycle(t)
        {
            let callee = Past::Trait(t.clone(), name);
            return crossing(callee, msig, ty, own);
        }
        let own_hidden = {
            let packs = self.pack_kinds(&msig, own, None);
            self.generic_args(&msig.type_params, &packs, own)
        };
        if param {
            return self.param_target(t, name, ty, own, (index, msig, own_hidden));
        }
        match self.impl_of(t, ty) {
            Some(ImplRef::Written { trait_item, owner }) => {
                let decls = self.decls();
                let imp = decls.trait_impl(&trait_item, &owner).cloned();
                if calls_own(&decls, &trait_item, &owner, name) {
                    let mut hidden = self.impl_args(imp.as_ref(), ty);
                    hidden.extend(own_hidden);
                    let mut targs = imp
                        .as_ref()
                        .map(|i| self.impl_targs(i, ty))
                        .unwrap_or_default();
                    targs.extend_from_slice(own);
                    let f = FnRef::ImplMethod(trait_item, owner, name);
                    // The descriptors of the impl's arguments its methods reflect on
                    // (meta.types-without-shape and meta.unseen-instantiations).
                    if let Some(sig) = super::functions::signature(&self.decls(), &f) {
                        hidden.extend(self.descriptor_args(&f, &sig, &targs));
                    }
                    Target::Direct(self.instance(f, &targs), hidden)
                } else {
                    self.default_target(&trait_item, name, ty, own, own_hidden)
                }
            }
            Some(ImplRef::Structural { trait_item, shape }) => {
                let mut hidden: Vec<Arg> = self
                    .structural_env(ty)
                    .into_iter()
                    .map(|(v, _)| Arg::Borrow(v))
                    .collect();
                hidden.extend(own_hidden);
                let mut targs = match ty {
                    _ if shape == Shape::Pack => Vec::new(),
                    Ty::Con(_, args) | Ty::Tuple(args) => args.clone(),
                    _ => Vec::new(),
                };
                targs.extend_from_slice(own);
                let f = FnRef::Structural(trait_item, name, shape);
                Target::Direct(self.instance(f, &targs), hidden)
            }
            None => Target::Direct(FnRef::Main, Vec::new()),
        }
    }

    /// Method `index` of trait `t`, of signature `msig`, on a type parameter: the impl's method
    /// if the instance knows the parameter's constructor, and otherwise its dictionary's, past
    /// the caps if the dictionary's entry can't take its own type arguments in one word.
    fn param_target(
        &mut self,
        t: &Item,
        name: Name,
        ty: &Ty,
        own: &[Ty],
        (index, msig, own_hidden): (u32, FnSig, Vec<Arg>),
    ) -> Target {
        if let Some(target) = self.known_target(t, name, ty, own, own_hidden.clone()) {
            return target;
        }
        let dict = self.dict(ty, t);
        // A dictionary's entry holds the method's own type parameters in one word, so a type
        // argument of several words crosses into it boxed.
        // A projection isn't bridged (`trait_target`): one with type parameters of its own
        // goes through the dictionary with them held in one word.
        let crosses = |o: &Ty| !self.one_word(o) || self.grows(o);
        if keyed(&self.decls(), t) && !msig.projection && own.iter().any(crosses) {
            return crossing(Past::Method(dict, index), msig, ty, own);
        }
        Target::Method(dict, index, own_hidden, Box::new(msig))
    }

    /// A trait's default method, for a receiver of type `ty` whose impl lacks the method: it
    /// takes the witness and dictionary of `Self`, or for a constructor trait is compiled for
    /// the receiver's constructor, then the witnesses of the arguments that the receiver's impl
    /// gives the trait's parameters.
    fn default_target(
        &mut self,
        t: &Item,
        name: Name,
        ty: &Ty,
        own: &[Ty],
        own_hidden: Vec<Arg>,
    ) -> Target {
        let constructor = self.decls().trait_info(t).is_some_and(|i| i.arity > 0);
        let args = self.trait_args_of(ty, t);
        let (mut hidden, self_targ) = if constructor {
            let head = match ty {
                Ty::Con(item, _) => Ty::Con(item.clone(), Vec::new()),
                other => other.clone(),
            };
            (self.param_witnesses(t, &args), head)
        } else {
            let given = (self.witness(ty), self.dict(ty, t));
            (self.default_hidden(t, ty, given, &args), ty.clone())
        };
        hidden.extend(own_hidden);
        let targs: Vec<Ty> = std::iter::once(self_targ)
            .chain(args)
            .chain(own.to_vec())
            .collect();
        let f = FnRef::DefaultMethod(t.clone(), name);
        Target::Direct(self.instance(f, &targs), hidden)
    }

    /// The hidden arguments of a trait's default method that a type `ty` gives, whose witness
    /// and dictionary of `t` are `given`: those of `Self`, and `Self`'s descriptor where the
    /// trait's defaults read it, then those of the arguments `args` that it gives the trait's
    /// parameters ().
    pub(crate) fn default_hidden(
        &mut self,
        t: &Item,
        ty: &Ty,
        (witness, dict): (Operand, Operand),
        args: &[Ty],
    ) -> Vec<Arg> {
        let mut hidden = vec![Arg::Borrow(witness), Arg::Borrow(dict)];
        if self.carried().self_of(t) {
            hidden.push(Arg::Borrow(self.descriptor(ty)));
        }
        hidden.extend(self.param_witnesses(t, args));
        hidden
    }

    /// The witness of each argument that a type gives the parameters of trait `t`, with its
    /// descriptor where the trait's defaults read it.
    fn param_witnesses(&mut self, t: &Item, args: &[Ty]) -> Vec<Arg> {
        let params = self.decls().trait_info(t).map(|i| i.params.clone());
        let params = params.unwrap_or_default();
        let mut hidden = Vec::new();
        for (i, a) in args.iter().enumerate() {
            hidden.push(Arg::Borrow(self.witness(a)));
            if params.get(i).is_some_and(|p| self.carried().generic(p)) {
                hidden.push(Arg::Borrow(self.descriptor(a)));
            }
        }
        hidden
    }

    /// The arguments that a type gives the parameters of a trait, through its impl or its
    /// bound (traits.trait-arguments), none for a trait without parameters.
    pub(crate) fn trait_args_of(&self, ty: &Ty, t: &Item) -> Vec<Ty> {
        let decls = self.decls();
        let table = stilt_types::ty::Table::default();
        let args = stilt_types::params::Args {
            decls: &decls,
            scope: &self.bound_args,
            table: &table,
        };
        if let stilt_types::params::TraitArgs::Known(args) = args.of(ty, t) {
            args
        } else {
            let n = decls.trait_info(t).map_or(0, |i| i.params.len());
            vec![Ty::Error; n]
        }
    }

    /// The type arguments of a written impl's generics, for the type `ty` it is used at, the
    /// member types its bounds give among them (traits.member-types).
    pub(crate) fn impl_targs(&self, imp: &ImplInfo, ty: &Ty) -> Vec<Ty> {
        let decls = self.decls();
        let table = stilt_types::ty::Table::default();
        stilt_types::params::Args {
            decls: &decls,
            scope: &self.bound_args,
            table: &table,
        }
        .impl_targs(imp, ty)
    }

    /// The method of a trait with methods of their own type parameters, on a type parameter
    /// whose constructor the instance knows: the impl's method, compiled for the layouts of its
    /// type arguments, its own included, with the impl's environment read from the parameter's
    /// dictionary, or the trait's default.
    fn known_target(
        &mut self,
        t: &Item,
        name: Name,
        ty: &Ty,
        own: &[Ty],
        own_hidden: Vec<Arg>,
    ) -> Option<Target> {
        let (con, args) = self.generic(ty)?.known.clone()?;
        let decls = self.decls();
        if !keyed(&decls, t) {
            return None;
        }
        if !calls_own(&decls, t, &con, name) {
            // The default takes the descriptors of the trait's arguments where it reads them,
            // which the dictionary's entry gives.
            let params = decls.trait_info(t).map(|i| i.params.clone());
            if params
                .unwrap_or_default()
                .iter()
                .any(|p| self.carried().generic(p))
            {
                return None;
            }
            return Some(self.default_target(t, name, ty, own, own_hidden));
        }
        let imp = decls.trait_impl(t, &con)?.clone();
        let f = FnRef::ImplMethod(t.clone(), con, name);
        let needs = self.needs(&f);
        let positions = impl_positions(&imp.self_ty, &imp.generics);
        let mut held: Vec<Held> = positions
            .iter()
            .zip(&needs)
            .map(|(k, need)| {
                let arg = k.and_then(|k| args.get(k)).unwrap_or(&Held::Word);
                (if need.is_empty() { arg.layout() } else { arg }).clone()
            })
            .collect();
        let own_needs = needs.get(imp.generics.len()..).unwrap_or(&[]);
        let keys = |capped| -> Vec<Held> {
            own.iter()
                .enumerate()
                .map(|(i, o)| self.key(o, own_needs.get(i).map_or(&[][..], Vec::as_slice), capped))
                .collect()
        };
        let mut own_held = keys(false);
        if self.past_known(&own_held, &f) {
            own_held = keys(true);
        }
        held.extend(own_held);
        let mut hidden = self.known_env(t, ty, &imp);
        hidden.extend(own_hidden);
        hidden.extend(self.known_descriptors(t, ty, &imp, &f));
        Some(Target::Direct(FnRef::instance(f, held), hidden))
    }

    /// The environment of the impl of trait `t` that the dictionary of the type parameter `ty`
    /// holds after its methods, as hidden arguments.
    fn known_env(&mut self, t: &Item, ty: &Ty, imp: &ImplInfo) -> Vec<Arg> {
        let dict = match self.dict(ty, t) {
            Operand::Local(d) => d,
            other @ Operand::Const(_) => self.b.define(Repr::Heap, Rvalue::Use(other)),
        };
        let methods = self.decls().trait_info(t).map_or(0, |i| i.methods.len());
        let words: usize = imp.generics.iter().map(|(_, b)| 1 + b.len()).sum();
        let len = u32::try_from(methods + words).expect("under 4G fields");
        let mut next = u32::try_from(methods).expect("under 4G methods");
        let mut env = Vec::new();
        for (_, bounds) in &imp.generics {
            for k in 0..=bounds.len() {
                let repr = if k == 0 { Repr::Scalar } else { Repr::Heap };
                let field = self.borrowed_field(dict, len, next, repr);
                env.push(Arg::Borrow(Operand::Local(field)));
                next += 1;
            }
        }
        env
    }

    /// The descriptors that the dictionary of the type parameter `ty` holds after the environment
    /// of its impl of `t`, which the impl's method `f` takes (meta.unseen-instantiations).
    fn known_descriptors(&mut self, t: &Item, ty: &Ty, imp: &ImplInfo, f: &FnRef) -> Vec<Arg> {
        let FnRef::ImplMethod(_, owner, _) = f else {
            return Vec::new();
        };
        let described = self.impl_described(t, owner);
        if described.is_empty() {
            return Vec::new();
        }
        let dict = match self.dict(ty, t) {
            Operand::Local(d) => d,
            other @ Operand::Const(_) => self.b.define(Repr::Heap, Rvalue::Use(other)),
        };
        let methods = self.decls().trait_info(t).map_or(0, |i| i.methods.len());
        let words: usize = imp.generics.iter().map(|(_, b)| 1 + b.len()).sum();
        let len = u32::try_from(methods + words + described.len()).expect("under 4G fields");
        let mut next = u32::try_from(methods + words).expect("under 4G fields");
        (0..described.len())
            .map(|_| {
                let field = self.borrowed_field(dict, len, next, Repr::Heap);
                next += 1;
                Arg::Borrow(Operand::Local(field))
            })
            .collect()
    }

    /// The impl of a trait for the constructor of a type, if it has one.
    pub(crate) fn impl_of(&self, t: &Item, ty: &Ty) -> Option<ImplRef> {
        let shape = match ty {
            Ty::Con(item, _) => {
                if self.decls().trait_impl(t, item).is_some() {
                    return Some(ImplRef::Written {
                        trait_item: t.clone(),
                        owner: item.clone(),
                    });
                }
                Shape::Con(item.clone())
            }
            Ty::Tuple(_) if super::packs::is_dynamic_tuple(ty) => Shape::Pack,
            Ty::Tuple(ts) => Shape::Tuple(u32::try_from(ts.len()).expect("under 4G elements")),
            _ => return None,
        };
        Some(ImplRef::Structural {
            trait_item: t.clone(),
            shape,
        })
    }

    /// The hidden arguments of a written impl's generics, for a receiver of type `ty`.
    pub(crate) fn impl_args(&mut self, imp: Option<&ImplInfo>, ty: &Ty) -> Vec<Arg> {
        let Some(imp) = imp else { return Vec::new() };
        let targs = self.impl_targs(imp, ty);
        self.generic_args(&imp.generics.clone(), &[], &targs)
    }
}

/// The place of each of an impl's generics among the arguments of the constructor it is for
/// (traits.implementing-trait).
pub(crate) fn impl_positions(self_ty: &hir::Ty, generics: &Bounds) -> Vec<Option<usize>> {
    let hir::Ty::Con(_, params) = self_ty else {
        return vec![None; generics.len()];
    };
    generics
        .iter()
        .map(|(g, _)| {
            params
                .iter()
                .position(|p| matches!(p, hir::Ty::Param(q) if q == g))
        })
        .collect()
}

/// A call past the caps of a trait's method of signature `sig`, on a receiver of type `ty`,
/// with its own type arguments `own`.
fn crossing(callee: Past, sig: FnSig, ty: &Ty, own: &[Ty]) -> Target {
    Target::Crossing(Box::new(Crossing {
        callee,
        sig,
        self_ty: Some(ty.clone()),
        targs: own.to_vec(),
        reflected: Vec::new(),
    }))
}
