//! The code that generic code, closures and natives reach a function through: a dictionary's
//! entries, and the code of a function, a dictionary's method or a variant used as a value.

use stilt_hir::decls::{FnSig, Lookup, TraitMethod, prelude_item};
use stilt_hir::hir::{Item, Mode};
use stilt_types::ty::{Passing, Ty, own_row};

use super::{shape_params, shape_type};
use crate::FnRef;
use crate::items::ImplRef;
use crate::lower::bridge::{Crossing, Past};
use crate::lower::calls::{Forms, Target, error_type};
use crate::lower::dicts::PRELUDE_TRAITS;
use crate::lower::functions::{holds_method, signature, trait_method};
use crate::lower::raises::raises_to_slot;
use crate::lower::{Conv, Cx, Form, Lower};
use crate::mir::{Arg, Function, Local, Operand, ParamMode, Repr};

/// The entry of method `index` of an impl's dictionary: it reads the impl's environment from
/// the dictionary, and calls the impl's method, or the trait's default, compiled for the layouts
/// of the impl's type arguments, which the entry is compiled for too. It takes a value of `Self`
/// or of a type parameter in one word, lent in a box if it has several, and an `inout` one
/// through a pointer to its words, gives one in the words that hold it ([`Forms::method`]), and
/// converts them for the method it calls.
pub(crate) fn entry(cx: &Cx<'_>, f: &FnRef, imp: &ImplRef, index: u32) -> Option<Function> {
    let decls = cx.decls();
    let (ImplRef::Written { trait_item: t, .. } | ImplRef::Structural { trait_item: t, .. }) = imp;
    let t = t.clone();
    let info = decls.trait_info(&t)?;
    let methods = u32::try_from(info.methods.len()).ok()?;
    let method = info.methods.get(index as usize)?.clone();
    let mut l = Lower::new(cx, f.clone(), true);
    let dict = l.b.param(Repr::Heap, ParamMode::Borrowed, None);
    l.count_call(f);
    let (env, self_ty, descs) = entry_env(&mut l, imp, dict, methods)?;
    let witness = l.witness(&self_ty);
    l.self_generic(witness.clone(), Operand::Local(dict), &t);
    let own = l.own_generics(&method.signature);
    let (overrides, own_method) = holds_method(&decls, imp, method.name)?;
    // The panic that stands for a method the impl lacks takes `Self` in one word, as the entry
    // does (program.meeting-the-error-type).
    let unboxes = overrides || !own_method;
    let view = unboxes.then_some(&self_ty);
    let hidden = (env, witness, Operand::Local(dict));
    let (target, mut args) = entry_target(&mut l, imp, &method, &self_ty, hidden, own_method);
    let forms = l.forms_of(&Target::Direct(target.clone(), Vec::new()));
    // Callers take and give values as the trait's signature says, in which its parameters are
    // type variables, and the impl's method as the impl's arguments for them say.
    let given = Forms::method(&method.signature);
    let sig = impl_signature(&decls, imp, &method);
    let values = adapted_params(&mut l, &sig, view, &forms, |i| {
        if unboxes {
            given.param(i)
        } else {
            Form::Layout
        }
    });
    args.extend(own);
    if matches!(target.generic(), FnRef::ImplMethod(..)) {
        args.extend(descs);
    }
    args.extend(values);
    let sig = &sig;
    let mut ret = Ty::from_hir(&sig.ret, Some(&self_ty));
    // A projection's entry passes the caller's access on, and gives nothing back
    // (projections.declaring-projection and projections.yield).
    if sig.projection {
        let access = l.b.param(Repr::Heap, ParamMode::Borrowed, None);
        args.push(Arg::Borrow(Operand::Local(access)));
        ret = Ty::unit();
    }
    let row = Passing::of(sig, Some(&self_ty)).row;
    l.ret = Conv {
        ty: ret.clone(),
        form: given.ret,
    };
    l.err = Conv {
        ty: error_type(&row),
        form: given.err,
    };
    l.raises_to_slot = raises_to_slot(sig);
    l.tail_call(Target::Direct(target, Vec::new()), args, &ret, &row);
    Some(l.into_function())
}

/// A trait's method as an impl's entry sees it: the trait's parameters replaced by the
/// impl's arguments for them, which name the impl's generics (traits.trait-arguments).
fn impl_signature(decls: &dyn Lookup, imp: &ImplRef, method: &TraitMethod) -> FnSig {
    let ImplRef::Written { trait_item, owner } = imp else {
        return method.signature.clone();
    };
    let params = decls
        .trait_info(trait_item)
        .map(|i| i.params.clone())
        .unwrap_or_default();
    let args = decls
        .trait_impl(trait_item, owner)
        .map(|i| i.trait_args.clone())
        .unwrap_or_default();
    let types: Vec<_> = params.into_iter().zip(args).collect();
    stilt_hir::decls::substituted(&method.signature, &types)
}

/// What an entry of a dictionary calls, compiled for the layouts of the impl's type arguments
/// and its own, and the hidden arguments of its impl that it passes: the impl's method with the
/// impl's environment, or the trait's default with the witness of `Self` and the dictionary.
fn entry_target(
    l: &mut Lower<'_>,
    imp: &ImplRef,
    method: &TraitMethod,
    self_ty: &Ty,
    (env, witness, dict): (Vec<Arg>, Operand, Operand),
    own_method: bool,
) -> (FnRef, Vec<Arg>) {
    let name = method.name;
    let own_targs = method
        .signature
        .type_params
        .iter()
        .map(|(g, _)| Ty::Param(g.clone()));
    let (target, targs, hidden) = match imp {
        ImplRef::Written { trait_item, owner } if own_method => {
            let target = FnRef::ImplMethod(trait_item.clone(), owner.clone(), name);
            (target, l.impl_type_args(imp, self_ty), env)
        }
        ImplRef::Written { trait_item, owner } => {
            let args: Vec<Ty> = l
                .decls()
                .trait_impl(trait_item, owner)
                .map(|i| i.trait_args.iter().map(|a| Ty::from_hir(a, None)).collect())
                .unwrap_or_default();
            let hidden = l.default_hidden(trait_item, self_ty, (witness, dict), &args);
            let target = FnRef::DefaultMethod(trait_item.clone(), name);
            let targs = std::iter::once(self_ty.clone()).chain(args).collect();
            (target, targs, hidden)
        }
        ImplRef::Structural { trait_item, shape } => (
            FnRef::Structural(trait_item.clone(), name, shape.clone()),
            l.impl_type_args(imp, self_ty),
            env,
        ),
    };
    let targs: Vec<Ty> = targs.into_iter().chain(own_targs).collect();
    (l.instance(target, &targs), hidden)
}

/// Adds the value parameters of a signature, `Self` being `view` where it is known, each in the
/// form that `from` says the caller gives it in, and returns the arguments that pass them on in
/// the forms `to` gives.
fn adapted_params(
    l: &mut Lower<'_>,
    sig: &FnSig,
    view: Option<&Ty>,
    to: &Forms,
    from: impl Fn(usize) -> Form,
) -> Vec<Arg> {
    sig.params
        .iter()
        .enumerate()
        .flat_map(|(i, (mode, t))| {
            let ty = Ty::from_hir(t, view);
            let args = l.adapted_param(*mode, &ty, from(i), to.param(i));
            // A dictionary's method takes an `inout` value of `Self` as a pointer to its words.
            match &args[..] {
                [Arg::Ref(p)] if to.self_words(i) => {
                    vec![Arg::Ref(l.words_pointer(p.clone(), &ty))]
                }
                _ => args,
            }
        })
        .collect()
}

/// The environment a dictionary holds after its `methods` methods, as hidden arguments, with
/// the impl's generics taken from it, the type the impl is for, and the descriptors of the
/// impl's type parameters that its methods take (meta.unseen-instantiations).
fn entry_env(
    l: &mut Lower<'_>,
    imp: &ImplRef,
    dict: Local,
    methods: u32,
) -> Option<(Vec<Arg>, Ty, Vec<Arg>)> {
    let decls = l.decls();
    let (generics, self_ty): (Vec<(Ty, Vec<Item>)>, Ty) = match imp {
        ImplRef::Written { trait_item, owner } => {
            let info = decls.trait_impl(trait_item, owner)?;
            let generics = info
                .generics
                .iter()
                .map(|(g, traits)| (Ty::Param(g.clone()), traits.clone()))
                .collect();
            (generics, Ty::from_hir(&info.self_ty, None))
        }
        ImplRef::Structural { shape, .. } => {
            let params = shape_params(&decls, shape);
            let traits: Vec<Item> = PRELUDE_TRAITS.iter().map(|n| prelude_item(n)).collect();
            let generics = params
                .iter()
                .map(|g| (Ty::Param(g.clone()), traits.clone()))
                .collect();
            (generics, shape_type(shape, &params))
        }
    };
    // A type's pack holds a witness and dictionaries for each of its elements (variadics.packs).
    let pack = matches!(imp, ImplRef::Structural { shape: crate::items::Shape::Con(item), .. }
        if crate::lower::packs::has_pack(&decls, item));
    let last = generics.len().saturating_sub(1);
    let arity = |k: usize| match l.held.get(k) {
        Some(crate::Held::Pack(Some(es))) if pack && k == last => es.len(),
        _ => 1,
    };
    let words: usize = generics
        .iter()
        .enumerate()
        .map(|(k, (_, traits))| (1 + traits.len()) * arity(k))
        .sum();
    let described = l.written_described(imp);
    let len = methods + u32::try_from(words + described.len()).ok()?;
    let start = l.generics.len();
    let mut next = methods;
    for (k, (ty, traits)) in generics.into_iter().enumerate() {
        match ty {
            Ty::Param(g) if pack && k == last => {
                l.type_pack_from(&g, &traits, (dict, len), &mut next);
            }
            ty => l.generic_from(ty, &traits, dict, len, &mut next),
        }
    }
    let descs = l.descriptors_from(&described, (dict, len), &mut next);
    let self_ty = l.cons.ty(&self_ty);
    Some((l.generic_hidden(start), self_ty, descs))
}

/// The signature of a function used as a value, and the type `Self` stands for in it, where
/// the function knows it.
fn value_signature(cx: &Cx<'_>, target: &FnRef) -> Option<(FnSig, Option<Ty>)> {
    match target {
        FnRef::Structural(t, name, shape) => {
            let params = shape_params(&cx.decls(), shape);
            let sig = trait_method(&cx.decls(), t, *name).map(|(_, s)| s)?;
            Some((sig, Some(shape_type(shape, &params))))
        }
        _ => signature(&cx.decls(), target).map(|s| (s, None)),
    }
}

/// The code of a function used as a value: it reads the function's hidden arguments from the
/// closure, and calls it, compiled for the layouts of its type arguments as the function is. It
/// takes and gives every value in the words that hold it where a type parameter stands, as a
/// closure's code does.
pub(crate) fn value(cx: &Cx<'_>, f: &FnRef, target: &FnRef) -> Option<Function> {
    let (sig, view) = value_signature(cx, target)?;
    let mut l = Lower::new(cx, f.clone(), true);
    let env = l.b.param(Repr::Heap, ParamMode::Borrowed, None);
    l.count_call(f);
    let generics = value_generics(cx, target, &sig);
    let described = l.described_params(target, &sig);
    let words = l.generic_words(generics.iter().map(|(ty, traits)| (ty, &traits[..])));
    let len = u32::try_from(words + 1 + described.len()).ok()?;
    let mut next = 1;
    for (ty, traits) in generics {
        l.generic_from(ty, &traits, env, len, &mut next);
    }
    let mut hidden = l.generic_hidden(0);
    // The descriptors it takes after them.
    hidden.extend(l.descriptors_from(&described, (env, len), &mut next));
    let target = FnRef::instance(target.clone(), f.held().to_vec());
    let forms = l.forms_of(&Target::Direct(target.clone(), Vec::new()));
    let values = adapted_params(&mut l, &sig, view.as_ref(), &forms, |_| Form::Layout);
    let ret = Ty::from_hir(&sig.ret, view.as_ref());
    let row = Passing::of(&sig, view.as_ref()).row;
    l.ret = Conv::of(ret.clone());
    l.err = Conv::boxed(error_type(&row));
    l.raises_to_slot = true;
    let params: Vec<Ty> = sig
        .params
        .iter()
        .map(|(_, t)| Ty::from_hir(t, view.as_ref()))
        .collect();
    if let Some(v) = l.inlined(&target, &values, (&params, &ret, &row)) {
        l.return_(v);
        return Some(l.into_function());
    }
    let mut all = hidden;
    all.extend(values);
    l.tail_call(Target::Direct(target, Vec::new()), all, &ret, &row);
    Some(l.into_function())
}

/// The generics whose witnesses and dictionaries a function takes before its own arguments, in
/// order, each with the traits of its dictionaries.
fn value_generics(cx: &Cx<'_>, target: &FnRef, sig: &FnSig) -> Vec<(Ty, Vec<Item>)> {
    let mut out = Vec::new();
    let decls = cx.decls();
    match target {
        // A constructor trait's `Self` takes no witness, and the trait's parameters take
        // theirs after it.
        FnRef::DefaultMethod(t, _) => {
            let info = decls.trait_info(t);
            if info.is_none_or(|i| i.arity == 0) {
                out.push((Ty::SelfTy, vec![t.clone()]));
            }
            for p in info.map(|i| i.params.clone()).unwrap_or_default() {
                out.push((Ty::Param(p), Vec::new()));
            }
        }
        FnRef::Structural(_, _, shape) => {
            let traits: Vec<Item> = PRELUDE_TRAITS.iter().map(|n| prelude_item(n)).collect();
            for g in shape_params(&cx.decls(), shape) {
                out.push((Ty::Param(g), traits.clone()));
            }
        }
        _ => {}
    }
    for (g, traits) in &sig.type_params {
        if !crate::lower::cons::is_constructor(&decls, traits) {
            out.push((Ty::Param(g.clone()), traits.clone()));
        }
    }
    out
}

/// The code of a dictionary's method used as a value: it calls the method of the dictionary
/// the closure holds, which takes a value of `Self` of the witness the closure holds.
pub(crate) fn method(cx: &Cx<'_>, f: &FnRef, t: &Item, index: u32) -> Option<Function> {
    let decls = cx.decls();
    let method = decls.trait_info(t)?.methods.get(index as usize)?.clone();
    let sig = &method.signature;
    let mut l = Lower::new(cx, f.clone(), true);
    let env = l.b.param(Repr::Heap, ParamMode::Borrowed, None);
    let own_tys: Vec<(Ty, &[Item])> = sig
        .type_params
        .iter()
        .map(|(g, traits)| (Ty::Param(g.clone()), &traits[..]))
        .collect();
    let own = l.generic_words(own_tys.iter().map(|(ty, traits)| (ty, *traits)));
    let len = u32::try_from(own + 3).ok()?;
    let dict = l.borrowed_field(env, len, 1, Repr::Heap);
    let witness = l.borrowed_field(env, len, 2, Repr::Scalar);
    l.push_generic(
        Ty::SelfTy,
        witness,
        vec![(t.clone(), Operand::Local(dict))],
        None,
    );
    let start = l.generics.len();
    let mut next = 3;
    for (g, traits) in &sig.type_params {
        l.generic_from(Ty::Param(g.clone()), traits, env, len, &mut next);
    }
    let own: Vec<Ty> = sig
        .type_params
        .iter()
        .map(|(g, _)| Ty::Param(g.clone()))
        .collect();
    if own.iter().any(|o| !l.one_word(o)) {
        return Some(method_past_caps(l, sig, (dict, index), own));
    }
    let hidden = l.generic_hidden(start);
    let target = Target::Method(
        Operand::Local(dict),
        index,
        Vec::new(),
        Box::new(sig.clone()),
    );
    let forms = l.forms_of(&target);
    let values = adapted_params(&mut l, sig, None, &forms, |_| Form::Layout);
    let ret = Ty::from_hir(&sig.ret, None);
    let row = own_row(sig);
    l.ret = Conv::of(ret.clone());
    l.err = Conv::boxed(error_type(&row));
    l.raises_to_slot = true;
    let mut all = hidden;
    all.extend(values);
    l.tail_call(target, all, &ret, &row);
    Some(l.into_function())
}

/// The code of a dictionary's method used as a value whose own type arguments have several
/// words, which the method's entry, compiled once for them, can't take: it calls the entry as
/// a call past the caps does, with those arguments crossing boxed.
fn method_past_caps(
    mut l: Lower<'_>,
    sig: &FnSig,
    (dict, index): (Local, u32),
    own: Vec<Ty>,
) -> Function {
    let passing = Passing::of(sig, None);
    let given = passing
        .params
        .iter()
        .map(|(mode, ty)| super::crossing::received(&mut l, *mode, ty, Form::Layout))
        .collect();
    let ret = Ty::from_hir(&sig.ret, None);
    l.ret = Conv::of(ret.clone());
    l.err = Conv::boxed(error_type(&passing.row));
    l.raises_to_slot = true;
    let c = Crossing {
        callee: Past::Method(Operand::Local(dict), index),
        sig: sig.clone(),
        self_ty: Some(Ty::SelfTy),
        targs: own,
        reflected: Vec::new(),
    };
    let loc = Operand::Local(l.loc);
    let v = l.cross_call(&c, given, loc, &passing.row, &ret);
    l.return_(v);
    l.into_function()
}

/// The code of a variant used as a value: it builds the variant from its arguments, compiled
/// for the layouts of its type's arguments, whose dynamic words the closure's witnesses tell,
/// and gives it in the words that hold it where a type parameter stands.
pub(crate) fn constructor(cx: &Cx<'_>, f: &FnRef, item: &Item) -> Option<Function> {
    let decls = cx.decls();
    let variant = decls.variant(item)?.clone();
    let params = decls.type_info(&variant.ty)?.params.clone();
    let mut l = Lower::new(cx, f.clone(), true);
    let env = l.b.param(Repr::Heap, ParamMode::Borrowed, None);
    let len = u32::try_from(params.len() + 1).ok()?;
    let mut next = 1;
    for g in &params {
        l.generic_from(Ty::Param(g.clone()), &[], env, len, &mut next);
    }
    let values: Vec<Vec<Operand>> = variant
        .payload
        .iter()
        .map(|t| {
            let ty = Ty::from_hir(t, None);
            l.adapted_param(Mode::Let, &ty, Form::Layout, Form::Layout)
                .into_iter()
                .flat_map(|a| a.operands().into_iter().cloned().collect::<Vec<_>>())
                .collect()
        })
        .collect();
    let ty = Ty::Con(
        variant.ty.clone(),
        params.into_iter().map(Ty::Param).collect(),
    );
    let words = l.build(&ty, variant.index as usize, values);
    l.ret = Conv::of(ty);
    l.raises_to_slot = true;
    l.return_(words);
    Some(l.into_function())
}

/// The code of a closure that a native calls with `n` arguments, each in one word, as natives
/// give values (`stilt_runtime::abi`): it calls the closure it holds with their words, held as
/// where a type parameter stands, and gives its result in one word, or for a result of several
/// words, writes them to the memory that its last parameter points to, which holds zeros. The
/// closure holds, after the code and the closure it calls, the witness of each parameter's type
/// and of the result's, which the code is compiled for the layouts of.
pub(crate) fn lent(cx: &Cx<'_>, f: &FnRef, n: u32) -> Option<Function> {
    let mut l = Lower::new(cx, f.clone(), true);
    let env = l.b.param(Repr::Heap, ParamMode::Borrowed, None);
    let len = n + 3;
    let closure = l.borrowed_field(env, len, 1, Repr::Heap);
    let mut next = 2;
    let types: Vec<Ty> = (0..=n)
        .map(|i| Ty::Param(super::made_up_generic(i)))
        .collect();
    for ty in &types {
        l.generic_from(ty.clone(), &[], env, len, &mut next);
    }
    let (params, ret) = types.split_at(n as usize);
    let args: Vec<Arg> = params
        .iter()
        .flat_map(|ty| l.adapted_param(Mode::Let, ty, Form::Word, Form::Layout))
        .collect();
    let ret = ret.first()?.clone();
    let out = (!l.one_word(&ret)).then(|| l.b.param(Repr::Scalar, ParamMode::Borrowed, None));
    l.ret = Conv::boxed(ret.clone());
    l.err = Conv::boxed(Ty::Error);
    l.raises_to_slot = true;
    let callee = crate::mir::Callee::Value(Operand::Local(closure));
    let loc = Operand::Local(l.loc);
    let (held, err) = (Conv::of(ret.clone()), Conv::boxed(Ty::Error));
    let v = l.finish_call(callee, args, &[], loc, true, &held, &err);
    if let Some(out) = out {
        l.store_words(&Operand::Local(out), v, &ret);
        l.ret = Conv::of(Ty::unit());
        l.return_(vec![Operand::word(0)]);
    } else {
        l.return_(v);
    }
    Some(l.into_function())
}
