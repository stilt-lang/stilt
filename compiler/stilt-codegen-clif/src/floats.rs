//! `f64` values in float registers (goal debug-speed). A local that holds an `f64`, as
//! `stilt_mir::floats` infers, is a Cranelift `F64` variable, so float arithmetic on it needs
//! no move between an integer register and a float one. A value meets a word only where a call
//! or a parameter passes it as one, or a runtime function takes one, and is converted there by
//! a bitcast. Memory takes it as it is, by float loads and stores.

#[cfg(test)]
mod tests;

use cranelift_codegen::ir::immediates::Ieee64;
use cranelift_codegen::ir::types::{F32, F64, I32, I64};
use cranelift_codegen::ir::{InstBuilder, Type, Value};
use stilt_mir::mir::{Const, Function, Local, NumKind, Operand};

use crate::module::typed_signature;
use crate::translate::Translator;

/// The type of each local of `f`: `F64` for one that holds an `f64` (`stilt_mir::floats`), and
/// `I64` for every other.
pub(crate) fn local_types(f: &Function) -> Vec<Type> {
    (stilt_mir::floats::f64_locals(f).into_iter())
        .map(|float| if float { F64 } else { I64 })
        .collect()
}

impl Translator<'_, '_> {
    /// `v` as a value of type `ty`, which has its size: itself, or its bits reinterpreted.
    pub(crate) fn converted(&mut self, v: Value, ty: Type) -> Value {
        if self.fb.func.dfg.value_type(v) == ty {
            v
        } else {
            self.fb.ins().bitcast(ty, self.plain, v)
        }
    }

    /// `v` as a word.
    pub(crate) fn word(&mut self, v: Value) -> Value {
        self.converted(v, I64)
    }

    /// The value `v` of the local `l`, as a word. The word holds the local's bits as well, and
    /// a debugger reads them there once the float is dead, as it is after its last conversion
    /// when Cranelift merges the conversions of one value into one.
    pub(crate) fn local_word(&mut self, l: Local, v: Value) -> Value {
        let word = self.word(v);
        if word != v && self.f.locals[l.0 as usize].shown.is_some() {
            self.labels
                .push((word, crate::debug::word_label(self.f, l)));
        }
        word
    }

    /// The value of an operand as its local holds it, an `f64` or a word, for memory to take as
    /// it is.
    pub(crate) fn held(&mut self, o: &Operand) -> Result<Value, String> {
        match o {
            Operand::Local(l) => Ok(self.use_local(*l)),
            Operand::Const(_) => self.operand(o),
        }
    }

    /// The value of an operand for a local of type `ty`: a constant word made a float of the
    /// same bits for an `F64` local, and otherwise as its local holds it.
    pub(crate) fn typed_operand(&mut self, o: &Operand, ty: Type) -> Result<Value, String> {
        match o {
            Operand::Const(Const::Word(w)) if ty == F64 => {
                Ok(self.fb.ins().f64const(Ieee64::with_bits(*w)))
            }
            _ => self.held(o),
        }
    }

    /// The value of an operand of float kind `kind`, as a float: an `f32` is held in the low
    /// bits of a word.
    pub(crate) fn float_operand(&mut self, o: &Operand, kind: NumKind) -> Result<Value, String> {
        if kind == NumKind::F32 {
            let word = self.operand(o)?;
            let bits = self.fb.ins().ireduce(I32, word);
            return Ok(self.fb.ins().bitcast(F32, self.plain, bits));
        }
        let v = self.typed_operand(o, F64)?;
        Ok(self.converted(v, F64))
    }

    /// The result of a float operation of kind `kind`: an `f64` as it is, and an `f32` in the
    /// low bits of a word.
    pub(crate) fn float_value(&mut self, kind: NumKind, x: Value) -> Value {
        if kind == NumKind::F32 {
            let bits = self.fb.ins().bitcast(I32, self.plain, x);
            self.fb.ins().uextend(I64, bits)
        } else {
            x
        }
    }

    /// A float of kind `kind` widened to an `f64`, which keeps its value.
    pub(crate) fn widened(&mut self, kind: NumKind, x: Value) -> Value {
        if kind == NumKind::F32 {
            self.fb.ins().fpromote(F64, x)
        } else {
            x
        }
    }

    /// The result of an operation of kind `kind` computed on widened operands, which has the
    /// value of one of that kind: an `f32`'s narrowed into the low bits of a word.
    pub(crate) fn narrowed(&mut self, kind: NumKind, x: Value) -> Value {
        if kind == NumKind::F32 {
            let n = self.fb.ins().fdemote(F32, x);
            self.float_value(kind, n)
        } else {
            x
        }
    }

    /// Calls a runtime function that takes `f64`s in float registers, and returns a value of
    /// type `returns`.
    pub(crate) fn float_runtime(
        &mut self,
        name: &str,
        args: &[Value],
        returns: Type,
    ) -> Result<Value, String> {
        let params: Vec<Type> = args.iter().map(|_| F64).collect();
        let sig = typed_signature(self.module, &params, &[returns]);
        let call = self.call_runtime(name, &sig, args)?;
        Ok(self.fb.inst_results(call)[0])
    }
}
