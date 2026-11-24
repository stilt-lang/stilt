//! The code that values crossing into code past the caps of instances reach, and come back
//! through (`crate::lower::bridge`): the entries of the dictionaries that a crossing type
//! argument is given for its bounds, which take a value of `Self` in its box and call the
//! method of the argument's own dictionary on its words; the functions that rebuild the nodes of
//! a value of a recursive type; and the code of the closures that convert what the closures they
//! hold take and give.

use stilt_hir::decls::Lookup;
use stilt_hir::hir::{Item, Mode};
use stilt_types::ty::{Passing, Ty};

use crate::lower::bridge::{Bridged, Dir, Given, Witnesses};
use crate::lower::calls::{Forms, Target, error_type};
use crate::lower::raises::raises_to_slot;
use crate::lower::{Conv, Cx, Form, Lower};
use crate::mir::{Arg, Function, Local, Operand, ParamMode, Repr};
use crate::{Cross, FnRef, Held, Word};

/// Entry `index` of the dictionary of trait `t` for a type argument that crosses boxed, held
/// outside in `words`: it converts each value whose type holds `Self` out of the code past the
/// caps, calls the method of the argument's own dictionary, which the dictionary holds after its
/// entries with the argument's witness, and converts the result and the error back in.
pub(crate) fn forward(
    cx: &Cx<'_>,
    f: &FnRef,
    t: &Item,
    index: u32,
    words: &[Word],
) -> Option<Function> {
    let decls = cx.decls();
    let info = decls.trait_info(t)?;
    let methods = u32::try_from(info.methods.len()).ok()?;
    let sig = info.methods.get(index as usize)?.signature.clone();
    let mut l = Lower::new(cx, f.clone(), true);
    let (inner, n) = forwarded(&mut l, t, methods, words);
    let own = l.own_generics(&sig);
    let given = Forms::method(&sig);
    let (pn, pu) = (
        Passing::of(&sig, Some(&n)),
        Passing::of(&sig, Some(&Ty::SelfTy)),
    );
    let args = pn
        .params
        .iter()
        .zip(&pu.params)
        .enumerate()
        .map(|(i, ((mode, nt), (_, ut)))| {
            // An `inout` value of `Self` comes as a pointer to the words of the type that
            // crosses, which its own dictionary's method takes alike.
            let ut = if given.self_words(i) { nt } else { ut };
            (
                received(&mut l, *mode, ut, given.param(i)),
                nt.clone(),
                ut.clone(),
            )
        })
        .collect();
    let (ret_n, ret_u) = (
        Ty::from_hir(&sig.ret, Some(&n)),
        Ty::from_hir(&sig.ret, Some(&Ty::SelfTy)),
    );
    let errs = pn
        .row
        .raise
        .as_deref()
        .cloned()
        .zip(pu.row.raise.as_deref().cloned());
    l.ret = Conv {
        ty: ret_u.clone(),
        form: given.ret,
    };
    l.err = Conv {
        ty: error_type(&pu.row),
        form: given.err,
    };
    l.raises_to_slot = raises_to_slot(&sig);
    let target = Target::Method(Operand::Local(inner), index, own, Box::new(sig.clone()));
    let loc = Operand::Local(l.loc);
    let call = Bridged::Target(target, pn.row.clone());
    let out = l.bridged_call(call, args, Dir::Out, (&ret_n, &ret_u), errs, loc);
    l.return_(out);
    Some(l.into_function())
}

/// Brings into scope, for the entry of a forwarding dictionary of trait `t`, of `methods`
/// methods, `Self` held in its box and a generic held in `words` that stands for the type that
/// crosses, with its own dictionary, which the forwarding one holds after its entries with the
/// type's witness. Returns that dictionary and the generic.
fn forwarded(l: &mut Lower<'_>, t: &Item, methods: u32, words: &[Word]) -> (Local, Ty) {
    let dict = l.b.param(Repr::Heap, ParamMode::Borrowed, None);
    let len = methods + 2;
    let inner = l.borrowed_field(dict, len, methods, Repr::Heap);
    let witness = l.borrowed_field(dict, len, methods + 1, Repr::Scalar);
    let n = l.cross_generic();
    let held = crate::lower::bridge::held_of_words(words);
    let inner_dicts = vec![(t.clone(), Operand::Local(inner))];
    l.push_generic(n.clone(), witness, inner_dicts, Some(&held));
    let own_dicts = vec![(t.clone(), Operand::Local(dict))];
    l.push_generic(Ty::SelfTy, witness, own_dicts, Some(&Held::Word));
    l.crossing.push((Ty::SelfTy, n.clone()));
    (inner, n)
}

/// Adds the parameters of a value of type `ty` passed in `mode`, given in `form`, and returns
/// how the value is given: its words, or for an `inout` one, the pointer to them.
pub(crate) fn received(l: &mut Lower<'_>, mode: Mode, ty: &Ty, form: Form) -> Given {
    if mode == Mode::Inout {
        let p = l.b.param(Repr::Scalar, ParamMode::Ref, None);
        return Given::Pointer(Operand::Local(p));
    }
    let reprs = match form {
        Form::Layout => l.layout(ty),
        Form::Word => vec![l.repr(ty)],
    };
    let params: Vec<_> = reprs
        .into_iter()
        .map(|r| l.b.param(r, ParamMode::Borrowed, None))
        .collect();
    let words = if form != Form::Layout && params.len() == 1 && !l.one_word(ty) {
        l.unbox_lasting(params[0], ty)
    } else {
        params.into_iter().map(Operand::Local).collect()
    };
    Given::Let(words)
}

/// The function that converts a value of the recursive type `cross` stands for into code past
/// the caps, or out of it: one level of its nodes, each of its fields of that type converted by
/// a call of itself.
pub(crate) fn rebuild(cx: &Cx<'_>, f: &FnRef, cross: &Cross, into: bool) -> Function {
    let mut l = Lower::new(cx, f.clone(), true);
    let (n, u) = l.cross_types(cross, &mut Witnesses::Params);
    let dir = if into { Dir::In } else { Dir::Out };
    let (from, to) = if into { (&n, &u) } else { (&u, &n) };
    let words: Vec<Operand> = l
        .layout(from)
        .into_iter()
        .map(|r| Operand::Local(l.b.param(r, ParamMode::Borrowed, None)))
        .collect();
    let out = l.convert_variants(&words, &n, &u, dir);
    l.ret = Conv::of(to.clone());
    l.return_(out);
    l.into_function()
}

/// The code of a closure that holds a closure of the function type `cross` stands for, and the
/// witnesses of its leaves: called on one side of the caps, it converts its arguments to the
/// other, calls the closure it holds, and converts the result and the error back.
pub(crate) fn adapt(cx: &Cx<'_>, f: &FnRef, cross: &Cross, into: bool) -> Option<Function> {
    let mut l = Lower::new(cx, f.clone(), true);
    let env = l.b.param(Repr::Heap, ParamMode::Borrowed, None);
    let len = u32::try_from(2 + leaves(cross)).ok()?;
    let held = l.borrowed_field(env, len, 1, Repr::Heap);
    let mut from = Witnesses::Env { env, len, next: 2 };
    let (n, u) = l.cross_types(cross, &mut from);
    let (Ty::Fn(nf), Ty::Fn(uf)) = (&n, &u) else {
        return None;
    };
    // Called past the caps, a closure from outside takes values held as past the caps.
    let (outer, dir) = if into {
        (&**uf, Dir::Out)
    } else {
        (&**nf, Dir::In)
    };
    // A closure of a polymorphic function type passes on the witnesses and dictionaries its
    // call gives.
    l.poly_params(outer);
    let hidden = outer
        .generics
        .iter()
        .flat_map(|(g, traits)| {
            let ty = Ty::Param(g.clone());
            let mut words = vec![Arg::Borrow(l.witness(&ty))];
            words.extend(traits.iter().map(|t| Arg::Borrow(l.dict(&ty, t))));
            words
        })
        .collect();
    let args = nf
        .params
        .iter()
        .zip(&uf.params)
        .zip(&outer.params)
        .map(|(((_, nt), (_, ut)), (mode, ot))| {
            (
                received(&mut l, *mode, ot, Form::Layout),
                nt.clone(),
                ut.clone(),
            )
        })
        .collect();
    let errs = nf
        .row
        .raise
        .as_deref()
        .cloned()
        .zip(uf.row.raise.as_deref().cloned());
    l.ret = Conv::of(outer.ret.clone());
    l.err = Conv::boxed(error_type(&outer.row));
    l.raises_to_slot = true;
    let loc = Operand::Local(l.loc);
    let call = Bridged::Closure(Operand::Local(held), hidden);
    let out = l.bridged_call(call, args, dir, (&nf.ret, &uf.ret), errs, loc);
    l.return_(out);
    Some(l.into_function())
}

/// The number of witnesses of a structure that the closure of [`adapt`] holds: one for each type
/// held alike on both sides, and one for each box.
fn leaves(c: &Cross) -> usize {
    match c {
        Cross::Same(_) => 1,
        Cross::Rigid(_) => 0,
        Cross::Poly(_, inner) => leaves(inner),
        Cross::Boxed(inner) => leaves(inner) + 1,
        Cross::Tuple(cs) | Cross::Con(_, cs) => cs.iter().map(leaves).sum(),
        Cross::Fn(ps, ret, err) => {
            ps.iter().map(|(_, c)| leaves(c)).sum::<usize>()
                + leaves(ret)
                + err.as_deref().map_or(0, leaves)
        }
    }
}
