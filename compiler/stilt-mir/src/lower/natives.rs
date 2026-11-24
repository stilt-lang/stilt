//! Calls of natives (std.natives): a native takes and gives a value of a type parameter in one
//! word, writes a result of several words of a type parameter, or the payload of an `Option` of
//! one, to memory that its caller passes a pointer to, and an error of several words to memory that
//! its caller passes a pointer to after it; and it calls a closure it is given with values in one
//! word (`stilt_runtime::abi`).

use stilt_hir::hir;
use stilt_types::ty::{FnTy, Ty};

use super::calls::is_var;
use super::functions::signature;
use super::places::Writeback;
use super::raises::raises_to_slot;
use super::{Conv, Lower};
use crate::FnRef;
use crate::items::{Code, code_of};
use crate::mir::{Arg, Callee, Const, Heapness, Local, Operand, Repr, Rvalue};

/// Where a call's error comes back, when it can raise.
pub(crate) enum Raised {
    /// In the words of the convention.
    Words(Conv),
    /// In these slots, which a native writes its error of several words to.
    Slots(Vec<Local>),
}

impl Lower<'_> {
    /// Whether a function is a native of the runtime, whose code is in the runtime.
    pub(crate) fn native(&self, f: &FnRef) -> bool {
        matches!(
            code_of(self.cx.db, self.cx.program, f.clone()),
            Some(Code::Native)
        )
    }

    /// Whether a function can raise at all: a native can only when its row says so, through
    /// its `raise` label or a row variable, as `List.sorted_by` raises what its key raises.
    pub(crate) fn may_raise(&self, f: &FnRef) -> bool {
        !self.native(f)
            || signature(&self.decls(), f)
                .is_some_and(|s| s.row.raise.is_some() || raises_to_slot(&s))
    }

    /// Calls the native `f`, passing it the memory for its result and its error that they
    /// need, and returns the words of its result.
    pub(crate) fn call_native(
        &mut self,
        callee: Callee,
        mut args: Vec<Arg>,
        (writebacks, loc): (&[Writeback], Operand),
        (f, raises): (&FnRef, bool),
        ret: &Conv,
        err: &Conv,
    ) -> Vec<Operand> {
        // A native that can raise returns one word of its result beside the raised flag, so it
        // writes the payload of an `Option` to memory however many words it has (views.consumers,
        // as `Iter.find` does).
        let raising = self.may_raise(f);
        self.scope_spawn(f);
        let out = match self.native_out(f, &ret.ty) {
            Some((elem, option)) if !self.one_word(&elem) || (option && raising) => {
                Some((self.slots(&mut args, &elem), option))
            }
            // The native takes the pointer all the same, which it doesn't use.
            Some(_) => {
                args.push(Arg::Borrow(Operand::word(0)));
                None
            }
            None => None,
        };
        let error_at = self.native_error(&mut args, f, err, raises);
        let Some((slots, option)) = out else {
            return self.call_raising(callee, args, writebacks, loc, ret, error_at);
        };
        let tag = Conv::of(Ty::unit());
        let first = self.call_raising(callee, args, writebacks, loc, &tag, error_at);
        let mut words = if option { first } else { Vec::new() };
        words.extend(self.take_slots(&slots));
        words
    }

    /// Passes the native `f` the memory for its error that it takes, and tells how its error
    /// comes back when the call can raise: an error of several words in memory, and one of one
    /// word in the word the native returns. A native whose error is a type parameter's value
    /// takes the memory whatever the error's layout, 0 for one of one word, so that its
    /// arguments are those its declaration fixes, as WebAssembly's calls check (wasm.target).
    fn native_error(
        &mut self,
        args: &mut Vec<Arg>,
        f: &FnRef,
        err: &Conv,
        raises: bool,
    ) -> Option<Raised> {
        let sig = signature(&self.decls(), f);
        if sig.as_ref().is_some_and(raises_to_slot) {
            return self.slot_for_error(args, err, raises);
        }
        if raises && !self.one_word(&err.ty) {
            return Some(Raised::Slots(self.slots(args, &err.ty)));
        }
        if sig.is_some_and(|s| s.row.raise.as_deref().is_some_and(is_var)) {
            args.push(Arg::Borrow(Operand::word(0)));
        }
        raises.then(|| Raised::Words(err.clone()))
    }

    /// The type of the value that a native whose result of type `ty` holds one writes to the
    /// memory its caller passes it a pointer to, after its arguments, if it has several words:
    /// a value of a type parameter, a tuple of them, or the payload of an `Option` of one or of
    /// a tuple, as `str.split_once` gives, which the native's result tells the tag of.
    fn native_out(&self, f: &FnRef, ty: &Ty) -> Option<(Ty, bool)> {
        let sig = signature(&self.decls(), f)?;
        match &sig.ret {
            t if is_var(t) => Some((ty.clone(), false)),
            // A pair of type parameters' values, as `par.both` gives (par.std-par).
            hir::Ty::Tuple(ts) if !ts.is_empty() && ts.iter().all(is_var) => {
                Some((ty.clone(), false))
            }
            hir::Ty::Con(item, args)
                if stilt_types::ty::is_prelude(item, "Option")
                    && matches!(args.as_slice(), [a] if is_var(a) || matches!(a, hir::Ty::Tuple(_))) =>
            {
                Some((super::lists::element_of(ty), true))
            }
            _ => None,
        }
    }

    /// Slots for the words of a value of type `ty`, which a native writes, each holding 0, and
    /// a pointer to them as the call's next argument.
    pub(crate) fn slots(&mut self, args: &mut Vec<Arg>, ty: &Ty) -> Vec<Local> {
        let zeros = vec![Operand::word(0); self.layout(ty).len()];
        let slots = self.copy_into_temps(zeros, ty);
        self.b.make_slots(&slots);
        let pointer = self.b.define_op(Repr::Scalar, Rvalue::SlotOf(slots[0]));
        args.push(Arg::Ref(pointer));
        slots
    }

    /// The words a native wrote to slots, which they give up: each slot holds 0 again.
    pub(crate) fn take_slots(&mut self, slots: &[Local]) -> Vec<Operand> {
        slots
            .iter()
            .map(|&s| {
                let repr = self.b.repr_of(s);
                let word = self.b.define_op(repr, Rvalue::Use(Operand::Local(s)));
                self.b.assign(s, Rvalue::Use(Operand::word(0)));
                word
            })
            .collect()
    }

    /// The value of a native that compiles inline, if `target` is one, on the arguments that the
    /// code of a function used as a value gives it, `values`, of types `params`.
    pub(crate) fn inlined(
        &mut self,
        target: &FnRef,
        values: &[Arg],
        (params, ret, row): (&[Ty], &Ty, &stilt_types::ty::Row),
    ) -> Option<Vec<Operand>> {
        let words: Vec<Operand> = values
            .iter()
            .flat_map(|a| a.operands().into_iter().cloned())
            .collect();
        self.inline_array(target.generic(), values, params, (ret, row))
            .or_else(|| self.inline_native(target, values, ret))
            .or_else(|| self.inline_window(target.generic(), values))
            .or_else(|| self.inline_view(target.generic(), &words))
    }

    /// A closure that a native can call, which takes and gives each value in one word: the
    /// closure itself when each has one word, and otherwise a closure whose code converts them
    /// for it ([`FnRef::Lent`]).
    ///
    /// A closure with an `inout` parameter is given as it is: the native passes it a pointer to
    /// the words of its layout, as `par.each` does an element's (par.writes-in-place).
    pub(crate) fn lent_closure(&mut self, closure: Operand, fty: &FnTy) -> Operand {
        if fty
            .params
            .iter()
            .any(|(mode, _)| *mode == stilt_hir::hir::Mode::Inout)
        {
            return closure;
        }
        let types: Vec<Ty> = fty
            .params
            .iter()
            .map(|(_, t)| t.clone())
            .chain(std::iter::once(fty.ret.clone()))
            .collect();
        let n = u32::try_from(fty.params.len()).expect("under 4G parameters");
        let code = self.instance(FnRef::Lent(n), &types);
        if code == FnRef::Lent(n) {
            return closure;
        }
        let mut env = vec![
            (Operand::Const(Const::Code(code)), Heapness::Static(false)),
            (closure, Heapness::Static(true)),
        ];
        for t in &types {
            let w = self.witness(t);
            env.push((w, Heapness::Static(false)));
        }
        self.alloc(0, env)
    }
}
