//! Cheaper checks for integer arithmetic with a constant operand, and for a division's overflow
//! (numbers.integer-panics). Cranelift fuses a comparison with the branch that tests it, one
//! compare and one conditional branch, while it materializes an overflow flag and tests it apart
//! (goal debug-speed):
//!
//! - `a + c` and `a - c` overflow exactly when `a` passes a bound that `c` gives, so the check
//!   compares `a` with it, and `c == 0` needs none;
//! - a division by a constant other than 0 and -1 can't fail, and one by -1 only overflows on
//!   the least value;
//! - a division by a variable tests for -1 first, on the hot path, and for the least value only
//!   in a cold block after it.
//!
//! Each check that remains panics as the general one does, at the same location and with the
//! same kind, so a program's report doesn't change.

#[cfg(test)]
mod tests;

use cranelift_codegen::ir::{InstBuilder, Value, condcodes::IntCC};
use stilt_mir::mir::{Const, NumKind, Operand, Prim};

use crate::prim::OVERFLOW;
use crate::translate::{Translator, UNREACHABLE};

/// The value of an integer constant of kind `kind`, as its words hold it.
fn constant(o: &Operand, kind: NumKind) -> Option<i128> {
    let Operand::Const(Const::Word(w)) = o else {
        return None;
    };
    Some(if kind.is_signed() {
        i128::from(w.cast_signed())
    } else {
        i128::from(*w)
    })
}

impl Translator<'_, '_> {
    /// The result of `op` on `args`, with the cheaper check of a constant operand, if `op` is
    /// an integer addition, subtraction, division or remainder with one.
    pub(crate) fn with_constant(
        &mut self,
        op: Prim,
        args: &[Operand],
        loc: &Operand,
    ) -> Result<Option<Value>, String> {
        let (Prim::Add(kind) | Prim::Sub(kind) | Prim::Div(kind) | Prim::Rem(kind)) = op else {
            return Ok(None);
        };
        let [x, y] = args else { return Ok(None) };
        if kind.is_float() {
            return Ok(None);
        }
        let (var, c) = match (constant(x, kind), constant(y, kind)) {
            (_, Some(c)) => (x, c),
            (Some(c), None) if matches!(op, Prim::Add(_)) => (y, c),
            _ => return Ok(None),
        };
        let a = self.operand(var)?;
        match op {
            Prim::Add(_) | Prim::Sub(_) => self.offset(op, kind, a, c, loc).map(Some),
            _ => self.divided_by(op, kind, a, c, loc),
        }
    }

    /// `a + c` or `a - c`, which overflows exactly when `a` passes the bound that keeps the
    /// result within the kind's range.
    fn offset(
        &mut self,
        op: Prim,
        kind: NumKind,
        a: Value,
        c: i128,
        loc: &Operand,
    ) -> Result<Value, String> {
        let c = if matches!(op, Prim::Sub(_)) { -c } else { c };
        let (min, max) = kind.range();
        let (high, low) = if kind.is_signed() {
            (IntCC::SignedGreaterThan, IntCC::SignedLessThan)
        } else {
            (IntCC::UnsignedGreaterThan, IntCC::UnsignedLessThan)
        };
        // `a + c` is above the maximum when `a > max - c`, and below the minimum when
        // `a < min - c`; each bound lies within the kind's range.
        let bad = match c.cmp(&0) {
            std::cmp::Ordering::Greater => Some((high, max - c)),
            std::cmp::Ordering::Less => Some((low, min - c)),
            std::cmp::Ordering::Equal => None,
        };
        if let Some((cc, bound)) = bad {
            let past = self.fb.ins().icmp_imm_s(cc, a, word(bound)?);
            self.panic_if(past, OVERFLOW, loc)?;
        }
        // The addition wraps, so the addend is `c` modulo 2^64: subtracting a constant of an
        // unsigned kind above 2^63, `c` being its negation, adds the word of `2^64 - c`.
        Ok(self.fb.ins().iadd_imm_s(a, word(c.rem_euclid(1 << 64))?))
    }

    /// `a / c` or `a % c` for a constant `c`: by 0, the general path, which panics; by -1 of a
    /// signed kind, an overflow on the least value; by any other, no check.
    fn divided_by(
        &mut self,
        op: Prim,
        kind: NumKind,
        a: Value,
        c: i128,
        loc: &Operand,
    ) -> Result<Option<Value>, String> {
        if c == 0 {
            return Ok(None);
        }
        if kind.is_signed() && c == -1 {
            let is_min = self
                .fb
                .ins()
                .icmp_imm_s(IntCC::Equal, a, word(kind.range().0)?);
            self.panic_if(is_min, OVERFLOW, loc)?;
        }
        let b = self
            .fb
            .ins()
            .iconst(cranelift_codegen::ir::types::I64, word(c)?);
        Ok(Some(match (op, kind.is_signed()) {
            (Prim::Div(_), true) => self.fb.ins().sdiv(a, b),
            (Prim::Div(_), false) => self.fb.ins().udiv(a, b),
            (_, true) => self.fb.ins().srem(a, b),
            (_, false) => self.fb.ins().urem(a, b),
        }))
    }

    /// Panics with an overflow at `loc` when `a` is the least value of `kind` and `b` is -1:
    /// the hot path tests `b`, and only a cold block tests `a`.
    pub(crate) fn least_by_minus_one(
        &mut self,
        kind: NumKind,
        a: Value,
        b: Value,
        loc: &Operand,
    ) -> Result<(), String> {
        let (rare, failed, join) = (
            self.fb.create_block(),
            self.fb.create_block(),
            self.fb.create_block(),
        );
        self.fb.set_cold_block(rare);
        self.fb.set_cold_block(failed);
        let minus_one = self.fb.ins().icmp_imm_s(IntCC::Equal, b, -1);
        self.fb.ins().brif(minus_one, rare, &[], join, &[]);
        self.fb.switch_to_block(rare);
        let is_min = self
            .fb
            .ins()
            .icmp_imm_s(IntCC::Equal, a, word(kind.range().0)?);
        self.fb.ins().brif(is_min, failed, &[], join, &[]);
        self.fb.switch_to_block(failed);
        self.panic(OVERFLOW, None, loc)?;
        self.fb.ins().trap(UNREACHABLE);
        self.fb.switch_to_block(join);
        Ok(())
    }
}

/// The 64-bit word of an integer within the range of a 64-bit kind, signed or not.
fn word(v: i128) -> Result<i64, String> {
    i64::try_from(v)
        .or_else(|_| u64::try_from(v).map(u64::cast_signed))
        .map_err(|_| format!("{v} is no word"))
}
