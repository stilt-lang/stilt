//! Primitive operations on numbers (numbers.numeric-types): arithmetic that panics on overflow and
//! on division by zero, wrapping arithmetic, shifts, comparisons and conversions.
//!
//! An integer of fewer than 64 bits is held sign- or zero-extended to 64, so arithmetic on two
//! of them can't overflow 64 bits, and a range check of the result finds an overflow of its
//! type. Arithmetic on 64-bit integers uses the instructions that report overflow, and a check
//! that fails panics on a cold path ([`crate::cold`]). A constant operand, and a division's
//! overflow, get cheaper checks ([`crate::checks`]). A float operation takes its operands as
//! floats, and gives an `f64` as one ([`crate::floats`]).

use cranelift_codegen::ir::{
    InstBuilder, Value,
    condcodes::{FloatCC, IntCC},
    types::{F32, F64, I8, I16, I32, I64},
};
use stilt_mir::mir::{NumKind, Operand, Prim};

use crate::translate::Translator;
use stilt_mir::floats::float_operands;

/// The runtime's numbers of the kinds of panic these operations raise (effects.panic-kinds).
pub(crate) const OVERFLOW: u64 = 0;
const DIVIDE_BY_ZERO: u64 = 1;

/// `Less`, `Equal` and `Greater`, as immediates.
const LESS: i64 = 1;
const EQUAL: i64 = 3;
const GREATER: i64 = 5;

impl Translator<'_, '_> {
    pub(crate) fn prim(
        &mut self,
        op: Prim,
        args: &[Operand],
        loc: &Operand,
    ) -> Result<Value, String> {
        if let Some(v) = self.with_constant(op, args, loc)? {
            return Ok(v);
        }
        // The operands of a float operation are floats; every other operation's are words.
        let float = float_operands(op);
        let values = args
            .iter()
            .map(|a| match float {
                Some(kind) => self.float_operand(a, kind),
                None => self.operand(a),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let a = values
            .first()
            .copied()
            .unwrap_or_else(|| self.fb.ins().iconst(I64, 0));
        let b = values.get(1).copied().unwrap_or(a);
        match op {
            Prim::Add(kind)
            | Prim::Sub(kind)
            | Prim::Mul(kind)
            | Prim::Div(kind)
            | Prim::Rem(kind) => self.arith(op, kind, a, b, loc),
            Prim::Neg(kind) => self.neg(kind, a, loc),
            Prim::AddWrap(kind) | Prim::SubWrap(kind) | Prim::MulWrap(kind) => {
                Ok(self.wrapping(op, kind, a, b))
            }
            Prim::DivByPositive(kind) | Prim::RemByPositive(kind) => {
                Ok(self.by_positive(op, kind, a, b))
            }
            Prim::AddUp(kind) => self.add_up(kind, a, b, loc),
            Prim::BitAnd => Ok(self.fb.ins().band(a, b)),
            Prim::BitOr => Ok(self.fb.ins().bor(a, b)),
            Prim::BitXor => Ok(self.fb.ins().bxor(a, b)),
            Prim::Not(kind) => {
                let n = self.fb.ins().bnot(a);
                Ok(self.wrap(kind, n))
            }
            Prim::BoolNot => Ok(self.fb.ins().bxor_imm_s(a, 1)),
            Prim::Shl(kind) | Prim::Shr(kind) => self.shift(op, kind, a, b, loc),
            Prim::Eq(kind) | Prim::Lt(kind) | Prim::Le(kind) => Ok(self.compare_op(op, kind, a, b)),
            Prim::WordEq => Ok(self.flag(IntCC::Equal, a, b)),
            Prim::Compare(kind) => self.three_way(kind, a, b),
            Prim::Widen(..) => Ok(a),
            Prim::Fits(from, to) => Ok(self.fits(from, to, a)),
            Prim::Wrap(_, to) => Ok(self.wrap(to, a)),
            Prim::ToFloat(from, to) => Ok(self.float_from(from, to, a)),
            Prim::FloatFits(from, to) => Ok(self.float_fits(from, to, a)),
            Prim::FloatToInt(from, to) => {
                let x = self.widened(from, a);
                Ok(if to.is_signed() {
                    self.fb.ins().fcvt_to_sint_sat(I64, x)
                } else {
                    self.fb.ins().fcvt_to_uint_sat(I64, x)
                })
            }
            _ => self.math(op, a, b, loc),
        }
    }

    fn flag(&mut self, cc: IntCC, a: Value, b: Value) -> Value {
        let c = self.fb.ins().icmp(cc, a, b);
        self.fb.ins().uextend(I64, c)
    }

    fn float_flag(&mut self, cc: FloatCC, a: Value, b: Value) -> Value {
        let c = self.fb.ins().fcmp(cc, a, b);
        self.fb.ins().uextend(I64, c)
    }

    /// A word of an integer of its kind, truncated to its width and extended again.
    pub(crate) fn wrap(&mut self, kind: NumKind, v: Value) -> Value {
        let narrow = match kind.bits() {
            8 => I8,
            16 => I16,
            32 => I32,
            _ => return v,
        };
        let short = self.fb.ins().ireduce(narrow, v);
        if kind.is_signed() {
            self.fb.ins().sextend(I64, short)
        } else {
            self.fb.ins().uextend(I64, short)
        }
    }

    /// Whether a word is outside the range of its kind, which has fewer than 64 bits.
    fn out_of_range(&mut self, kind: NumKind, v: Value) -> Value {
        let (min, max) = kind.range();
        let max = i64::try_from(max).expect("a small kind's maximum");
        if kind.is_signed() {
            let min = i64::try_from(min).expect("a small kind's minimum");
            let low = self.fb.ins().icmp_imm_s(IntCC::SignedLessThan, v, min);
            let high = self.fb.ins().icmp_imm_s(IntCC::SignedGreaterThan, v, max);
            self.fb.ins().bor(low, high)
        } else {
            self.fb.ins().icmp_imm_s(IntCC::UnsignedGreaterThan, v, max)
        }
    }

    fn arith(
        &mut self,
        op: Prim,
        kind: NumKind,
        a: Value,
        b: Value,
        loc: &Operand,
    ) -> Result<Value, String> {
        if kind.is_float() {
            return self.float_arith(op, kind, a, b);
        }
        match op {
            Prim::Div(_) | Prim::Rem(_) => self.division(op, kind, a, b, loc),
            _ if kind.bits() == 64 => {
                let (result, overflow) = match (op, kind.is_signed()) {
                    (Prim::Add(_), true) => self.fb.ins().sadd_overflow(a, b),
                    (Prim::Add(_), false) => self.fb.ins().uadd_overflow(a, b),
                    (Prim::Sub(_), true) => self.fb.ins().ssub_overflow(a, b),
                    (Prim::Sub(_), false) => self.fb.ins().usub_overflow(a, b),
                    (_, true) => self.fb.ins().smul_overflow(a, b),
                    (_, false) => self.fb.ins().umul_overflow(a, b),
                };
                self.panic_if(overflow, OVERFLOW, loc)?;
                Ok(result)
            }
            _ => {
                let result = match op {
                    Prim::Add(_) => self.fb.ins().iadd(a, b),
                    Prim::Sub(_) => self.fb.ins().isub(a, b),
                    _ => self.fb.ins().imul(a, b),
                };
                let bad = self.out_of_range(kind, result);
                self.panic_if(bad, OVERFLOW, loc)?;
                Ok(result)
            }
        }
    }

    /// `/` truncates toward zero, and `%` takes the dividend's sign
    /// (numbers.division-and-remainder).
    fn division(
        &mut self,
        op: Prim,
        kind: NumKind,
        a: Value,
        b: Value,
        loc: &Operand,
    ) -> Result<Value, String> {
        let zero = self.fb.ins().icmp_imm_s(IntCC::Equal, b, 0);
        self.panic_if(zero, DIVIDE_BY_ZERO, loc)?;
        if kind.is_signed() {
            self.least_by_minus_one(kind, a, b, loc)?;
        }
        Ok(match (op, kind.is_signed()) {
            (Prim::Div(_), true) => self.fb.ins().sdiv(a, b),
            (Prim::Div(_), false) => self.fb.ins().udiv(a, b),
            (_, true) => self.fb.ins().srem(a, b),
            (_, false) => self.fb.ins().urem(a, b),
        })
    }

    /// `a + b` of two integers that the optimizer proved at least 0: of 64 bits, their sum is
    /// below 2⁶⁴, so it overflows exactly when its sign bit is set, which one instruction tests
    /// and branches on.
    fn add_up(
        &mut self,
        kind: NumKind,
        a: Value,
        b: Value,
        loc: &Operand,
    ) -> Result<Value, String> {
        if kind.bits() != 64 || !kind.is_signed() {
            return self.arith(Prim::Add(kind), kind, a, b, loc);
        }
        let sum = self.fb.ins().iadd(a, b);
        let sign = self.fb.ins().band_imm_s(sum, i64::MIN);
        self.panic_if(sign, OVERFLOW, loc)?;
        Ok(sum)
    }

    /// `/` and `%` by a divisor that the optimizer proved positive, so neither 0 nor -1:
    /// nothing can fail, and nothing is checked.
    fn by_positive(&mut self, op: Prim, kind: NumKind, a: Value, b: Value) -> Value {
        match (op, kind.is_signed()) {
            (Prim::DivByPositive(_), true) => self.fb.ins().sdiv(a, b),
            (Prim::DivByPositive(_), false) => self.fb.ins().udiv(a, b),
            (_, true) => self.fb.ins().srem(a, b),
            (_, false) => self.fb.ins().urem(a, b),
        }
    }

    fn float_arith(
        &mut self,
        op: Prim,
        kind: NumKind,
        x: Value,
        y: Value,
    ) -> Result<Value, String> {
        let result = match op {
            Prim::Add(_) => self.fb.ins().fadd(x, y),
            Prim::Sub(_) => self.fb.ins().fsub(x, y),
            Prim::Mul(_) => self.fb.ins().fmul(x, y),
            Prim::Div(_) => self.fb.ins().fdiv(x, y),
            // The remainder, computed in `f64`, where an `f32`'s is exact too.
            _ => {
                let (x, y) = (self.widened(kind, x), self.widened(kind, y));
                let r = self.float_runtime("stilt_rt_fmod", &[x, y], F64)?;
                return Ok(self.narrowed(kind, r));
            }
        };
        Ok(self.float_value(kind, result))
    }

    fn neg(&mut self, kind: NumKind, a: Value, loc: &Operand) -> Result<Value, String> {
        if kind.is_float() {
            let n = self.fb.ins().fneg(a);
            return Ok(self.float_value(kind, n));
        }
        if kind.is_signed() {
            let min = i64::try_from(kind.range().0).expect("a signed minimum");
            let is_min = self.fb.ins().icmp_imm_s(IntCC::Equal, a, min);
            self.panic_if(is_min, OVERFLOW, loc)?;
        }
        let n = self.fb.ins().ineg(a);
        Ok(self.wrap(kind, n))
    }

    fn wrapping(&mut self, op: Prim, kind: NumKind, a: Value, b: Value) -> Value {
        let result = match op {
            Prim::AddWrap(_) => self.fb.ins().iadd(a, b),
            Prim::SubWrap(_) => self.fb.ins().isub(a, b),
            _ => self.fb.ins().imul(a, b),
        };
        self.wrap(kind, result)
    }

    /// A shift by an amount outside `0..bits` panics with `overflow` (numbers.shift-amounts).
    fn shift(
        &mut self,
        op: Prim,
        kind: NumKind,
        a: Value,
        b: Value,
        loc: &Operand,
    ) -> Result<Value, String> {
        let bits = i64::from(kind.bits());
        // The amount has an integer type of its own, whose word holds its value sign-extended
        // when the type is signed and zero-extended otherwise, so this one comparison finds an
        // amount that is negative in its type or at least the width of `kind`
        // (numbers.shift-amounts).
        let bad = self
            .fb
            .ins()
            .icmp_imm_s(IntCC::UnsignedGreaterThanOrEqual, b, bits);
        self.panic_if(bad, OVERFLOW, loc)?;
        Ok(match (op, kind.is_signed()) {
            (Prim::Shl(_), _) => {
                let result = self.fb.ins().ishl(a, b);
                self.wrap(kind, result)
            }
            (_, true) => self.fb.ins().sshr(a, b),
            (_, false) => self.fb.ins().ushr(a, b),
        })
    }

    fn compare_op(&mut self, op: Prim, kind: NumKind, a: Value, b: Value) -> Value {
        if kind.is_float() {
            let cc = match op {
                Prim::Eq(_) => FloatCC::Equal,
                Prim::Lt(_) => FloatCC::LessThan,
                _ => FloatCC::LessThanOrEqual,
            };
            return self.float_flag(cc, a, b);
        }
        let cc = match (op, kind.is_signed()) {
            (Prim::Eq(_), _) => IntCC::Equal,
            (Prim::Lt(_), true) => IntCC::SignedLessThan,
            (Prim::Lt(_), false) => IntCC::UnsignedLessThan,
            (_, true) => IntCC::SignedLessThanOrEqual,
            (_, false) => IntCC::UnsignedLessThanOrEqual,
        };
        self.flag(cc, a, b)
    }

    /// The order of two numbers as an `Ordering`: the total order of traits.floats on floats.
    fn three_way(&mut self, kind: NumKind, a: Value, b: Value) -> Result<Value, String> {
        if kind.is_float() {
            // Widening keeps an `f32`'s place in the order.
            let (x, y) = (self.widened(kind, a), self.widened(kind, b));
            return self.float_runtime("stilt_rt_float_compare", &[x, y], I64);
        }
        let (lt, gt) = if kind.is_signed() {
            (IntCC::SignedLessThan, IntCC::SignedGreaterThan)
        } else {
            (IntCC::UnsignedLessThan, IntCC::UnsignedGreaterThan)
        };
        let less = self.fb.ins().icmp(lt, a, b);
        let greater = self.fb.ins().icmp(gt, a, b);
        let less_word = self.fb.ins().iconst(I64, LESS);
        let equal_word = self.fb.ins().iconst(I64, EQUAL);
        let greater_word = self.fb.ins().iconst(I64, GREATER);
        let not_less = self.fb.ins().select(greater, greater_word, equal_word);
        Ok(self.fb.ins().select(less, less_word, not_less))
    }

    /// Whether an integer of kind `from` keeps its value as one of kind `to`.
    fn fits(&mut self, from: NumKind, to: NumKind, v: Value) -> Value {
        let (min, max) = to.range();
        let max = i64::try_from(max.min(i128::from(i64::MAX))).expect("clamped");
        let wide = to.bits() == 64;
        let result = match (from.is_signed(), to.is_signed()) {
            (true, true) if wide => self.fb.ins().iconst(I8, 1),
            (true, true) => {
                let min = i64::try_from(min).expect("a small minimum");
                let low = self
                    .fb
                    .ins()
                    .icmp_imm_s(IntCC::SignedGreaterThanOrEqual, v, min);
                let high = self
                    .fb
                    .ins()
                    .icmp_imm_s(IntCC::SignedLessThanOrEqual, v, max);
                self.fb.ins().band(low, high)
            }
            (true, false) => {
                let low = self
                    .fb
                    .ins()
                    .icmp_imm_s(IntCC::SignedGreaterThanOrEqual, v, 0);
                if wide {
                    low
                } else {
                    let high = self
                        .fb
                        .ins()
                        .icmp_imm_s(IntCC::SignedLessThanOrEqual, v, max);
                    self.fb.ins().band(low, high)
                }
            }
            (false, _) if wide && !to.is_signed() => self.fb.ins().iconst(I8, 1),
            (false, _) => self
                .fb
                .ins()
                .icmp_imm_s(IntCC::UnsignedLessThanOrEqual, v, max),
        };
        self.fb.ins().uextend(I64, result)
    }

    /// An integer or a float of kind `from` as a float of kind `to`; a float `v` is one.
    fn float_from(&mut self, from: NumKind, to: NumKind, v: Value) -> Value {
        let ty = if to == NumKind::F32 { F32 } else { F64 };
        let x = match (from.is_float(), from.is_signed()) {
            (false, true) => self.fb.ins().fcvt_from_sint(ty, v),
            (false, false) => self.fb.ins().fcvt_from_uint(ty, v),
            (true, _) => match (from, to) {
                (NumKind::F64, NumKind::F32) => self.fb.ins().fdemote(F32, v),
                (NumKind::F32, NumKind::F64) => self.fb.ins().fpromote(F64, v),
                _ => v,
            },
        };
        self.float_value(to, x)
    }

    /// Whether a float's truncation is a value of kind `to` (numbers.conversions).
    fn float_fits(&mut self, from: NumKind, to: NumKind, v: Value) -> Value {
        let x = self.widened(from, v);
        let t = self.fb.ins().trunc(x);
        let bits = to.bits();
        let (bottom, top) = if to.is_signed() {
            (
                -(2f64.powi(i32::try_from(bits - 1).unwrap_or(63))),
                2f64.powi(i32::try_from(bits - 1).unwrap_or(63)),
            )
        } else {
            (0.0, 2f64.powi(i32::try_from(bits).unwrap_or(64)))
        };
        let (bottom, top) = (self.fb.ins().f64const(bottom), self.fb.ins().f64const(top));
        let low = self.fb.ins().fcmp(FloatCC::GreaterThanOrEqual, t, bottom);
        let high = self.fb.ins().fcmp(FloatCC::LessThan, t, top);
        let both = self.fb.ins().band(low, high);
        self.fb.ins().uextend(I64, both)
    }

    /// `abs`, `min`, `max` and the float operations of std.floats and std.math.
    fn math(&mut self, op: Prim, a: Value, b: Value, loc: &Operand) -> Result<Value, String> {
        match op {
            Prim::Abs(kind) if !kind.is_float() => {
                if !kind.is_signed() {
                    return Ok(a);
                }
                let min = i64::try_from(kind.range().0).expect("a signed minimum");
                let is_min = self.fb.ins().icmp_imm_s(IntCC::Equal, a, min);
                self.panic_if(is_min, OVERFLOW, loc)?;
                Ok(self.fb.ins().iabs(a))
            }
            Prim::Min(kind) | Prim::Max(kind) if !kind.is_float() => {
                Ok(match (op, kind.is_signed()) {
                    (Prim::Min(_), true) => self.fb.ins().smin(a, b),
                    (Prim::Min(_), false) => self.fb.ins().umin(a, b),
                    (_, true) => self.fb.ins().smax(a, b),
                    (_, false) => self.fb.ins().umax(a, b),
                })
            }
            // Rounded in `f64`, where an `f32`'s rounding is exact too.
            Prim::Round(kind) => {
                let x = self.widened(kind, a);
                let r = self.float_runtime("stilt_rt_round", &[x], F64)?;
                Ok(self.narrowed(kind, r))
            }
            Prim::IsNan(_) => Ok(self.float_flag(FloatCC::Unordered, a, a)),
            Prim::Abs(kind)
            | Prim::Min(kind)
            | Prim::Max(kind)
            | Prim::Sqrt(kind)
            | Prim::Floor(kind)
            | Prim::Ceil(kind)
            | Prim::Trunc(kind) => {
                let result = match op {
                    Prim::Abs(_) => self.fb.ins().fabs(a),
                    Prim::Min(_) => self.fb.ins().fmin(a, b),
                    Prim::Max(_) => self.fb.ins().fmax(a, b),
                    Prim::Sqrt(_) => self.fb.ins().sqrt(a),
                    Prim::Floor(_) => self.fb.ins().floor(a),
                    Prim::Ceil(_) => self.fb.ins().ceil(a),
                    _ => self.fb.ins().trunc(a),
                };
                Ok(self.float_value(kind, result))
            }
            _ => unreachable!("an operation that `prim` handles"),
        }
    }
}
