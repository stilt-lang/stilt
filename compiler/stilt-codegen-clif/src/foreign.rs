//! Calls of foreign functions, which C gives (c.calls, c.finding-functions), with C's calling
//! convention for the target: each argument converted from the word compiled code holds it in to
//! what C takes, and the result back. In memory, and in an executable of a target whose executables
//! load libraries, the function is the one its name gives among those loaded, which the runtime
//! finds at its first call; an executable of a target whose executables load none imports it by its
//! name from the target's C library (c.build-targets).

use cranelift_codegen::ir::{InstBuilder, Value};
use stilt_mir::Foreign;
use stilt_mir::mir::{Arg, Const, Operand};

use crate::calls::{Results, Then};
use crate::library::{c_param, from_word, to_word};
use crate::translate::Translator;

impl Translator<'_, '_> {
    /// Calls the foreign function `c` with `args`, the location first, and gives `dest` its
    /// result.
    pub(crate) fn call_foreign(
        &mut self,
        c: &Foreign,
        args: &[Arg],
        (dest, next, raised): Then,
    ) -> Result<(), String> {
        let mut words = Vec::with_capacity(args.len());
        for a in args {
            let (Arg::Borrow(o) | Arg::Own(o) | Arg::Ref(o)) = a else {
                return Err(format!("a call of {} lends a value", c.name));
            };
            words.push(self.operand(o)?);
        }
        let Some((&loc, words)) = words.split_first() else {
            return Err(format!("a call of {} has no location", c.name));
        };
        let mut sig = self.module.make_signature();
        sig.params.extend(c.params.iter().map(|&t| c_param(t)));
        sig.returns.extend(c.result.map(c_param));
        let values: Vec<Value> = (words.iter().zip(&c.params))
            .map(|(&w, &t)| from_word(&mut self.fb, w, t))
            .collect();
        let call = if self.reg.object && self.static_target() {
            let id = self.reg.foreign(self.module, &c.name, &sig)?;
            let r = self.func_ref(id);
            self.fb.ins().call(r, &values)
        } else {
            let name = self.operand(&Operand::Const(Const::Str(c.name.as_str().into())))?;
            let address = self
                .runtime("stilt_rt_c_function", &[loc, name], true)?
                .ok_or("the runtime gives no address")?;
            let sig = self.fb.import_signature(sig);
            self.fb.ins().call_indirect(sig, address, &values)
        };
        let results = self.fb.inst_results(call).to_vec();
        let words: Vec<Value> = (results.iter().zip(c.result))
            .map(|(&v, t)| to_word(&mut self.fb, v, t))
            .collect();
        self.returned(&Results::Registers(words), None, dest, next, raised)
    }

    /// Whether the target's executables are static, and load no library: x86-64 Linux's.
    fn static_target(&self) -> bool {
        self.module.isa().triple().to_string().contains("linux")
    }
}
