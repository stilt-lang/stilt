//! Calls (values.inout-arguments and values.left-to-right; traits.method-resolution): resolving
//! what a call calls, evaluating its arguments from left to right, reading its `inout` places when
//! it starts, and writing them back when it returns or raises.
//!
//! A value goes to a callee as the words of its layout. Where the callee's declaration names a
//! type parameter or `Self`, generic code compiled for the layouts of its type arguments takes
//! the words that hold the value where a type parameter stands (`crate::layout`), and so does
//! the code of a closure, for every value. Natives and the methods of dictionaries take such a
//! value in one word: a value of several words is lent to them in a box on the caller's stack,
//! since they borrow it. A dictionary's method gives a result in the words that hold it, and a
//! native writes a result or an error of several words to memory that its caller passes
//! (`stilt_runtime::abi`).

use stilt_hir::decls::FnSig;
use stilt_hir::hir::{self, Mode};
use stilt_types::tast::{self, Callee as TCallee, Expr};
use stilt_types::ty::{Row, Tail, Ty};

use super::bridge::{Crossing, Past};
use super::functions::signature;
use super::natives::Raised;
use super::places::Writeback;
use super::words::{operands, word};
use super::{Conv, Form, Lower};
use crate::FnRef;
use crate::mir::{Arg, Callee, Operand, Terminator};

/// What a call calls, with the hidden arguments that come before its own.
pub(crate) enum Target {
    Direct(FnRef, Vec<Arg>),
    /// A method of a dictionary, with the method's own hidden arguments and its signature.
    Method(Operand, u32, Vec<Arg>, Box<FnSig>),
    /// A call past the caps of instances, some of whose type arguments cross boxed.
    Crossing(Box<super::bridge::Crossing>),
}

/// How a callee takes each value parameter, and gives its result and its error.
#[derive(Clone, Debug)]
pub(crate) struct Forms {
    pub(crate) params: Vec<Form>,
    pub(crate) ret: Form,
    pub(crate) err: Form,
    /// How it takes a parameter past `params`, as a closure takes every one.
    rest: Form,
    /// Whether each parameter is an `inout` one of a dictionary's method typed `Self`, whose
    /// argument goes as a pointer to its words, which a type parameter held in one word finds
    /// in its box ([`Lower::words_pointer`]).
    selves: Vec<bool>,
    /// Whether each parameter is in place, so that the storage of its `inout` argument is made
    /// unique at the call (facts.in-place-promise).
    pub(crate) unique: Vec<bool>,
}

/// Whether a type of a signature is a type variable.
pub(crate) fn is_var(t: &hir::Ty) -> bool {
    matches!(t, hir::Ty::Param(_) | hir::Ty::SelfTy)
}

impl Forms {
    /// The forms of a signature's values: those its declaration types by a type variable in
    /// `var`, the others in their layouts. An error that comes through a row variable, which may
    /// be any, comes in one word, or in the memory its caller provides (`super::raises`).
    pub(crate) fn of(sig: &FnSig, var: Form) -> Self {
        let pick = |t: &hir::Ty| if is_var(t) { var } else { Form::Layout };
        Self {
            params: sig.params.iter().map(|(_, t)| pick(t)).collect(),
            ret: pick(&sig.ret),
            err: sig.row.raise.as_deref().map_or(Form::Word, pick),
            rest: Form::Layout,
            selves: Vec::new(),
            unique: Vec::new(),
        }
    }

    /// The forms of a dictionary's method: a value its declaration types by a type variable is
    /// taken in one word, as the runtime passes it to the methods of the prelude's traits, but
    /// for an `inout` one of `Self`, which goes as a pointer to its words, and given in the words
    /// that hold it, so that a result of `Self` comes back unboxed.
    pub(crate) fn method(sig: &FnSig) -> Self {
        let mut forms = Self::of(sig, Form::Word);
        forms.selves = sig
            .params
            .iter()
            .map(|(mode, t)| *mode == Mode::Inout && matches!(t, hir::Ty::SelfTy))
            .collect();
        for (form, &own) in forms.params.iter_mut().zip(&forms.selves) {
            if own {
                *form = Form::Layout;
            }
        }
        if is_var(&sig.ret) {
            forms.ret = Form::Layout;
        }
        if sig.row.raise.as_deref().is_some_and(is_var) {
            forms.err = Form::Layout;
        }
        forms
    }

    /// Every value in its layout, and the error in one word, as a closure's code takes and
    /// gives them.
    pub(crate) fn layout() -> Self {
        Self {
            params: Vec::new(),
            ret: Form::Layout,
            err: Form::Word,
            rest: Form::Layout,
            selves: Vec::new(),
            unique: Vec::new(),
        }
    }

    pub(crate) fn param(&self, i: usize) -> Form {
        self.params.get(i).copied().unwrap_or(self.rest)
    }

    /// Whether parameter `i`, by its place among the source's, is in place
    /// (facts.in-place-promise).
    pub(crate) fn unique(&self, i: usize) -> bool {
        self.unique.get(i).copied().unwrap_or(false)
    }

    /// Whether parameter `i` is an `inout` one of a dictionary's method typed `Self`.
    pub(crate) fn self_words(&self, i: usize) -> bool {
        self.selves.get(i).copied().unwrap_or(false)
    }
}

/// Whether a call that performs this row can raise: through its `raise` label, through a row
/// variable, written or implicit, which may be instantiated with one (effects.row-variables), or
/// through an effect, whose handler may end its `with` with an abort (`super::handlers`).
pub(crate) fn can_raise(row: &Row) -> bool {
    row.raise.is_some() || !matches!(row.tail, Tail::Closed) || aborts(row)
}

/// Whether a row holds an effect whose handler may end a `with` early, by a raise
/// (handlers.resuming), or `async`, whose `await` so stops code the sequential run never reaches.
pub(crate) fn aborts(row: &Row) -> bool {
    !row.effects.is_empty()
}

impl Lower<'_> {
    pub(crate) fn call(
        &mut self,
        callee: &TCallee,
        targs: &[Ty],
        args: &[tast::Arg],
        row: &Row,
        e: &Expr,
    ) -> Vec<Operand> {
        if let TCallee::Operation(effect, op) = callee {
            return self.perform(effect, *op, args, row, e);
        }
        if let Some(v) = self.meta_call(callee, targs, args, row, e) {
            return v;
        }
        if let Some(v) = self.inline_call(callee, args, e) {
            return v;
        }
        if let Some(v) = self.view_call(callee, args, e) {
            return v;
        }
        if let Some(v) = self.window_call(callee, args, e) {
            return v;
        }
        if let Some(v) = self.array_call(callee, args, row, e) {
            return v;
        }
        let target = self.resolve(callee, targs);
        if let Target::Crossing(c) = &target {
            return self.call_crossing(c, args, row, e);
        }
        if let Some(c) = self.conversions(callee, targs) {
            return self.converted_call(target, &c, args, row, e);
        }
        let forms = self.forms_of(&target);
        let (values, writebacks) = self.scoped_arguments(callee, args, &forms);
        let loc = self.loc_at(e.at);
        self.emit_call(target, values, &writebacks, loc, can_raise(row), &e.ty, row)
    }

    pub(crate) fn call_value(&mut self, f: &Expr, args: &[tast::Arg], e: &Expr) -> Vec<Operand> {
        let closure = self.expr1(f);
        let (values, writebacks) = self.arguments(args, &Forms::layout());
        let loc = self.loc_at(e.at);
        let row = match &f.ty {
            Ty::Fn(fty) => fty.row.clone(),
            _ => Row::EMPTY,
        };
        let ret = Conv::of(e.ty.clone());
        let err = Conv::boxed(error_type(&row));
        let raises = can_raise(&row);
        self.finish_call(
            Callee::Value(closure),
            values,
            &writebacks,
            loc,
            raises,
            &ret,
            &err,
        )
    }

    /// What a call calls.
    pub(crate) fn resolve(&mut self, callee: &TCallee, targs: &[Ty]) -> Target {
        match callee {
            TCallee::Function(item) => self.direct(FnRef::Function(item.clone()), targs),
            TCallee::Member(owner, name) => self.direct(FnRef::Member(owner.clone(), *name), targs),
            TCallee::TraitMethod(t, name, ty) => self.trait_target(t, *name, ty, targs),
            TCallee::Operation(..) => unreachable!("`Lower::expr` lowers a performance"),
        }
    }

    /// A function with its type arguments: its instance, or a call past the caps when a type
    /// argument would grow its instances without end, within this function's cycle of the call
    /// graph, or is one of several words that the function reflects on (`super::bridge`).
    pub(crate) fn direct(&mut self, f: FnRef, targs: &[Ty]) -> Target {
        if let FnRef::Function(item) = &f
            && let Some(foreign) = self.foreign(item)
        {
            return Target::Direct(FnRef::Foreign(Box::new(foreign)), Vec::new());
        }
        let sig = signature(&self.decls(), &f);
        let native = self.native(&f);
        // A projection's access would cross with it, which the bridge doesn't convert: its
        // instances follow its type arguments.
        if let Some(sig) = &sig
            && !native
            && !sig.projection
        {
            let reflected = self.reflected_args(&f, sig, targs);
            if reflected.contains(&true)
                || (targs.iter().any(|a| self.grows(a)) && self.in_cycle(&f))
            {
                return Target::Crossing(Box::new(Crossing {
                    callee: Past::Function(f),
                    sig: sig.clone(),
                    self_ty: None,
                    targs: targs.to_vec(),
                    reflected,
                }));
            }
        }
        let hidden = sig.map_or_else(Vec::new, |sig| {
            let packs = self.pack_kinds(&sig, targs, Some(&f));
            let mut hidden = self.generic_args(&sig.type_params, &packs, targs);
            // The descriptors of the types it reflects on, or names.
            hidden.extend(self.descriptor_args(&f, &sig, targs));
            hidden
        });
        let f = if native { f } else { self.instance(f, targs) };
        Target::Direct(f, hidden)
    }

    /// Whether a target is a projection, which takes the caller's access as one more argument
    /// (projections.declaring-projection).
    pub(crate) fn target_is_projection(&self, target: &Target) -> bool {
        match target {
            Target::Direct(f, _) => {
                signature(&self.decls(), f.generic()).is_some_and(|s| s.projection)
            }
            Target::Method(.., sig) => sig.projection,
            Target::Crossing(c) => c.sig.projection,
        }
    }

    /// How the code a target calls takes and gives its values: a native in one word where the
    /// declaration names a type variable, a dictionary's method as [`Forms::method`] says, and
    /// the code of a generic function in the words of their layouts.
    pub(crate) fn forms_of(&self, target: &Target) -> Forms {
        match target {
            Target::Direct(f, _) => {
                // The natives of `std.array` compile inline, in the words of the layouts.
                let native = self.native(f) && super::arrays::array_native(f.generic()).is_none();
                let var = if native { Form::Word } else { Form::Layout };
                let sig = signature(&self.decls(), f.generic());
                let mut forms = sig
                    .as_ref()
                    .map_or_else(Forms::layout, |s| Forms::of(s, var));
                forms.unique = self.in_place(f);
                // A native gives back an error in one word, and calls a closure it is given
                // with values in one word.
                if native {
                    forms.err = Form::Word;
                    for (form, (_, t)) in forms
                        .params
                        .iter_mut()
                        .zip(sig.iter().flat_map(|s| &s.params))
                    {
                        if matches!(t, hir::Ty::Fn(_)) {
                            *form = Form::Word;
                        }
                    }
                }
                forms
            }
            Target::Method(.., sig) => Forms::method(sig),
            Target::Crossing(c) => Forms::method(&c.sig),
        }
    }

    /// Evaluates the arguments from left to right. An `inout` argument is a place, whose index
    /// expressions are evaluated in its turn, and which is read when the call starts, after every
    /// argument (values.left-to-right and values.index-reads). Each goes in the form that `forms`
    /// gives it.
    pub(crate) fn arguments(
        &mut self,
        args: &[tast::Arg],
        forms: &Forms,
    ) -> (Vec<Arg>, Vec<Writeback>) {
        let mut evaluated = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let form = forms.param(i);
            if let tast::ExprKind::Spread(s) = &a.value.kind {
                for (words, ty) in self.spread_values(s) {
                    evaluated.push(Ok(self.pass(words, &ty, Form::Layout)));
                }
                continue;
            }
            evaluated.push(match a.mode {
                Mode::Let => {
                    let words = self.expr(&a.value);
                    Ok(self.pass(words, &a.value.ty, form))
                }
                Mode::Inout => Err((self.place(&a.value), &a.value.ty, forms.self_words(i))),
            });
        }
        let mut values = Vec::new();
        let mut writebacks = Vec::new();
        for (i, a) in evaluated.into_iter().enumerate() {
            match a {
                Ok(passed) => values.extend(passed),
                Err((place, ty, self_words)) => {
                    let (slot, writeback) = self.inout(place);
                    if forms.unique(i) {
                        self.unique_slot(&slot);
                    }
                    let slot = if self_words {
                        self.words_pointer(slot, ty)
                    } else {
                        slot
                    };
                    values.push(Arg::Ref(slot));
                    writebacks.extend(writeback);
                }
            }
        }
        (values, writebacks)
    }

    /// The arguments that pass the words of a value of type `ty`, which the callee borrows, in
    /// the form `form`.
    pub(crate) fn pass(&mut self, words: Vec<Operand>, ty: &Ty, form: Form) -> Vec<Arg> {
        match (form, ty) {
            (Form::Layout, _) => words.into_iter().map(Arg::Borrow).collect(),
            (Form::Word, Ty::Fn(fty)) => vec![Arg::Borrow(self.lent_closure(word(&words, 0), fty))],
            (Form::Word, _) => vec![self.lend(words, ty)],
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn emit_call(
        &mut self,
        target: Target,
        values: Vec<Arg>,
        writebacks: &[Writeback],
        loc: Operand,
        raises: bool,
        ty: &Ty,
        row: &Row,
    ) -> Vec<Operand> {
        let forms = self.forms_of(&target);
        let to_slot = self.target_raises_to_slot(&target);
        // A projection raises what the caller's access raises (projections.raising-during-access).
        let raises = raises || self.target_is_projection(&target);
        let (callee, mut args, raises) = match target {
            Target::Direct(f, hidden) => {
                let raises = raises && self.may_raise(&f);
                (Callee::Direct(f), hidden, raises)
            }
            Target::Method(dict, index, hidden, _) => (Callee::Method(dict, index), hidden, raises),
            Target::Crossing(_) => {
                unreachable!("a call past the caps converts its arguments first")
            }
        };
        args.extend(values);
        let err = Conv {
            ty: error_type(row),
            form: forms.err,
        };
        let ret = Conv {
            ty: ty.clone(),
            form: forms.ret,
        };
        if let Callee::Direct(f) = &callee
            && self.native(f)
        {
            let f = f.clone();
            return self.call_native(callee, args, (writebacks, loc), (&f, raises), &ret, &err);
        }
        let error_at = if to_slot {
            self.slot_for_error(&mut args, &err, raises)
        } else {
            raises.then_some(Raised::Words(err))
        };
        self.call_raising(callee, args, writebacks, loc, &ret, error_at)
    }

    /// Emits a call of a closure, its first argument the location and its last the memory for
    /// an error of several words, and the write-back of its `inout` places on both ways out of
    /// it, and returns the words of its result.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn finish_call(
        &mut self,
        callee: Callee,
        mut args: Vec<Arg>,
        writebacks: &[Writeback],
        loc: Operand,
        may_raise: bool,
        ret: &Conv,
        err: &Conv,
    ) -> Vec<Operand> {
        let raised = self.slot_for_error(&mut args, err, may_raise);
        self.call_raising(callee, args, writebacks, loc, ret, raised)
    }

    /// Emits a call as [`Lower::finish_call`] does, whose error, if it can raise, comes back as
    /// `raised` says.
    pub(crate) fn call_raising(
        &mut self,
        callee: Callee,
        args: Vec<Arg>,
        writebacks: &[Writeback],
        loc: Operand,
        ret: &Conv,
        raised: Option<Raised>,
    ) -> Vec<Operand> {
        let dest = self.conv_temps(ret);
        let next = self.b.new_block();
        let error = raised.as_ref().map(|r| {
            let temps = match r {
                Raised::Words(err) => self.conv_temps(err),
                Raised::Slots(..) => self.conv_temps(&Conv::boxed(Ty::Error)),
            };
            (temps, self.b.new_block())
        });
        let mut all = vec![Arg::Borrow(loc)];
        all.extend(args);
        self.b.terminate(Terminator::Call {
            callee,
            args: all,
            dest: dest.clone(),
            next,
            raised: error.clone(),
        });
        if let (Some((temps, block)), Some(raised)) = (error, raised) {
            self.b.switch_to(block);
            self.write_back(writebacks);
            let words = match raised {
                Raised::Words(err) => self.received(operands(&temps), &err),
                Raised::Slots(slots) => self.take_slots(&slots),
            };
            self.raise(words);
        }
        self.b.switch_to(next);
        self.write_back(writebacks);
        if ret.ty == Ty::never() {
            self.b.terminate(Terminator::Unreachable);
        }
        self.received(operands(&dest), ret)
    }
}

/// The error a row raises: its `raise` label's type, or no known type, for a row variable.
pub(crate) fn error_type(row: &Row) -> Ty {
    row.raise.as_deref().cloned().unwrap_or(Ty::Error)
}
