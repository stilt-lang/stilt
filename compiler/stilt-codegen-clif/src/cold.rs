//! Failure paths: the code that ends the program when a check fails, such as an overflow, a
//! division by zero or an index out of bounds, and a panic the program writes
//! (program.panic-report). Each is a block that Cranelift lays out cold, after the rest of the
//! function, and that calls a runtime function that never returns, the panic entry or the one that
//! reports the failure, then ends in a trap. No value is live after that call, so no value of the
//! hot path has to survive it, and the register allocator keeps them in registers rather than
//! saving them around a call that only a failure makes (goal debug-speed).

#[cfg(test)]
mod tests;

use cranelift_codegen::ir::types::I64;
use cranelift_codegen::ir::{InstBuilder, Value};
use stilt_mir::mir::Operand;

use crate::translate::{Translator, UNREACHABLE};

impl Translator<'_, '_> {
    /// Ends the program through `fail` when `cond` is nonzero, `fail` calling a runtime
    /// function that never returns.
    pub(crate) fn fail_if(
        &mut self,
        cond: Value,
        fail: impl FnOnce(&mut Self) -> Result<(), String>,
    ) -> Result<(), String> {
        let (failed, ok) = (self.fb.create_block(), self.fb.create_block());
        self.fb.set_cold_block(failed);
        self.fb.ins().brif(cond, failed, &[], ok, &[]);
        self.fb.switch_to_block(failed);
        fail(self)?;
        self.fb.ins().trap(UNREACHABLE);
        self.fb.switch_to_block(ok);
        Ok(())
    }

    /// Ends the program with a panic of the runtime's kind number `kind` at `loc` when `cond`
    /// is nonzero.
    pub(crate) fn panic_if(&mut self, cond: Value, kind: u64, loc: &Operand) -> Result<(), String> {
        self.fail_if(cond, |t| t.panic(kind, None, loc))
    }

    /// Ends the program with a panic of the runtime's kind number `kind` at `loc`, whose detail
    /// is the string `detail`, or the kind's own detail.
    pub(crate) fn panic(
        &mut self,
        kind: u64,
        detail: Option<&Operand>,
        loc: &Operand,
    ) -> Result<(), String> {
        let loc = self.operand(loc)?;
        let kind = self.fb.ins().iconst(I64, i64::try_from(kind).unwrap_or(0));
        let detail = match detail {
            Some(d) => self.operand(d)?,
            None => self.fb.ins().iconst(I64, 0),
        };
        self.runtime("stilt_rt_panic", &[loc, kind, detail], false)?;
        Ok(())
    }
}
