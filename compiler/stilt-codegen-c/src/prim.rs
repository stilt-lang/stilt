//! Primitive operations on numbers (numbers.numeric-types), as C that reaches none of C's undefined
//! behaviour: arithmetic that panics on overflow through clang's checked builtins on the
//! operands' own C types; wrapping arithmetic on `u64`, truncated to the kind's width; a check
//! of each divisor, of `MIN / -1` and of each shift's amount before the operation; and a float's
//! truncation converted to an integer by a saturating conversion, which `FloatFits` guards. An
//! integer of fewer than 64 bits is held sign- or zero-extended to 64, as in debug builds.

use std::fmt::Write;

use stilt_mir::mir::{Local, NumKind, Operand, Prim};

use crate::function::{Emit, Expr};
use crate::proved::Proved;
use stilt_mir::floats::float_operands;

/// The runtime's numbers of the kinds of panic these operations raise (effects.panic-kinds).
pub(crate) const OVERFLOW: u64 = 0;
pub(crate) const DIVIDE_BY_ZERO: u64 = 1;

/// Where an operation panics, and which of its checks verification proves.
struct At {
    loc: String,
    proved: Proved,
}

/// The C type of a kind's values.
fn ctype(k: NumKind) -> &'static str {
    match k {
        NumKind::I8 => "i8",
        NumKind::I16 => "i16",
        NumKind::I32 => "i32",
        NumKind::I64 => "i64",
        NumKind::U8 => "u8",
        NumKind::U16 => "u16",
        NumKind::U32 => "u32",
        NumKind::U64 => "u64",
        NumKind::F32 => "float",
        NumKind::F64 => "double",
    }
}

/// A value of a kind's C type, extended to a word as the kind is.
fn extend(k: NumKind, e: &str) -> String {
    if k.is_signed() {
        format!("(u64)(i64)({e})")
    } else {
        format!("(u64)({e})")
    }
}

/// A word truncated to a kind's width and extended again.
fn wrap(k: NumKind, e: &str) -> String {
    if k.bits() == 64 {
        e.to_owned()
    } else {
        extend(k, &format!("({})({e})", ctype(k)))
    }
}

/// An integer literal of the signed word that holds `v`.
fn signed(v: i128) -> String {
    format!(
        "(i64){:#x}ULL",
        i64::try_from(v).unwrap_or(0).cast_unsigned()
    )
}

impl Emit<'_, '_> {
    /// Assigns the local `l` the result of `op`, after its checks.
    pub(crate) fn prim(
        &mut self,
        l: Local,
        op: Prim,
        args: &[Operand],
        loc: &Operand,
    ) -> Result<(), String> {
        let float = float_operands(op);
        let mut values = Vec::with_capacity(args.len());
        for a in args {
            let e = self.operand(a)?;
            values.push(match float {
                Some(NumKind::F32) => Expr::word(format!("lt_f32({})", e.w())),
                Some(_) => Expr::double(e.d()),
                None => Expr::word(e.w()),
            });
        }
        let at = At {
            loc: self.word(loc)?,
            proved: self.prog.proved(loc),
        };
        let zero = Expr::word("0");
        let a = values.first().cloned().unwrap_or(zero);
        let b = values.get(1).cloned().unwrap_or_else(|| a.clone());
        self.out.push_str("{ ");
        let e = match float {
            Some(kind) => float_op(op, kind, &a.text, &b.text),
            None => self.int_op(op, &a.text, &b.text, &at),
        };
        self.set(l, &e);
        self.out.push_str("}\n");
        Ok(())
    }

    /// Panics with `kind` where `at` is when `cond` holds, or, for a check that verification
    /// proves, lets clang take `cond` as false and drop the test (builds.dropped-checks).
    fn check(&mut self, cond: &str, kind: u64, at: &At) {
        if at.proved.rules_out(kind) {
            let _ = write!(self.out, "if ({cond}) __builtin_unreachable(); ");
        } else {
            let loc = &at.loc;
            let _ = write!(
                self.out,
                "if (LT_UNLIKELY({cond})) lt_panic({loc}, {kind}); "
            );
        }
    }

    fn int_op(&mut self, op: Prim, a: &str, b: &str, at: &At) -> Expr {
        let word = |s: String| Expr::word(s);
        match op {
            Prim::Add(k) | Prim::Sub(k) | Prim::Mul(k) => self.checked(op, k, a, b, at),
            Prim::AddUp(k) if k.bits() == 64 && k.is_signed() => {
                let _ = write!(self.out, "u64 s_ = {a} + {b}; ");
                self.check("s_ >> 63", OVERFLOW, at);
                word("s_".to_owned())
            }
            Prim::AddUp(k) => self.checked(Prim::Add(k), k, a, b, at),
            Prim::Div(k) | Prim::Rem(k) => self.division(op, k, a, b, at),
            Prim::DivByPositive(k) => word(extend(k, &format!("({0}){a} / ({0}){b}", ctype(k)))),
            Prim::RemByPositive(k) => word(extend(k, &format!("({0}){a} % ({0}){b}", ctype(k)))),
            Prim::Neg(k) => {
                if k.is_signed() {
                    self.check(
                        &format!("(i64){a} == {}", signed(k.range().0)),
                        OVERFLOW,
                        at,
                    );
                }
                word(wrap(k, &format!("(u64)0 - {a}")))
            }
            Prim::AddWrap(k) => word(wrap(k, &format!("{a} + {b}"))),
            Prim::SubWrap(k) => word(wrap(k, &format!("{a} - {b}"))),
            Prim::MulWrap(k) => word(wrap(k, &format!("{a} * {b}"))),
            Prim::BitAnd => word(format!("({a} & {b})")),
            Prim::BitOr => word(format!("({a} | {b})")),
            Prim::BitXor => word(format!("({a} ^ {b})")),
            Prim::Not(k) => word(wrap(k, &format!("~{a}"))),
            Prim::BoolNot => word(format!("({a} ^ 1)")),
            Prim::Shl(k) | Prim::Shr(k) => self.shift(op, k, a, b, at),
            Prim::WordEq => word(format!("(u64)({a} == {b})")),
            _ => self.int_compare(op, a, b, at),
        }
    }

    /// `+`, `-` and `*`, which panic on overflow of the operands' kind.
    fn checked(&mut self, op: Prim, k: NumKind, a: &str, b: &str, at: &At) -> Expr {
        let builtin = match op {
            Prim::Add(_) => "add",
            Prim::Sub(_) => "sub",
            _ => "mul",
        };
        let t = ctype(k);
        let cond = format!("__builtin_{builtin}_overflow(({t}){a}, ({t}){b}, &t_)");
        let _ = write!(self.out, "{t} t_; ");
        self.check(&cond, OVERFLOW, at);
        Expr::word(extend(k, "t_"))
    }

    /// `/` truncates toward zero, and `%` takes the dividend's sign
    /// (numbers.division-and-remainder), as C's do once the divisor is neither 0 nor, for the least
    /// value, -1.
    fn division(&mut self, op: Prim, k: NumKind, a: &str, b: &str, at: &At) -> Expr {
        self.check(&format!("{b} == 0"), DIVIDE_BY_ZERO, at);
        if k.is_signed() {
            let least = signed(k.range().0);
            let cond = format!("(i64){b} == -1 && (i64){a} == {least}");
            self.check(&cond, OVERFLOW, at);
        }
        let symbol = if matches!(op, Prim::Div(_)) { "/" } else { "%" };
        Expr::word(extend(k, &format!("({0}){a} {symbol} ({0}){b}", ctype(k))))
    }

    /// A shift by an amount outside `0..bits` panics with `overflow` (numbers.shift-amounts).
    fn shift(&mut self, op: Prim, k: NumKind, a: &str, b: &str, at: &At) -> Expr {
        self.check(&format!("{b} >= {}", k.bits()), OVERFLOW, at);
        Expr::word(match (op, k.is_signed()) {
            (Prim::Shl(_), _) => wrap(k, &format!("{a} << {b}")),
            (_, true) => format!("(u64)((i64){a} >> {b})"),
            (_, false) => format!("({a} >> {b})"),
        })
    }

    /// Comparisons, conversions, `abs`, `min` and `max` of integers.
    fn int_compare(&mut self, op: Prim, lhs: &str, rhs: &str, at: &At) -> Expr {
        let ord = |kind: NumKind, v: &str| {
            if kind.is_signed() {
                format!("(i64){v}")
            } else {
                v.to_owned()
            }
        };
        Expr::word(match op {
            Prim::Eq(_) => format!("(u64)({lhs} == {rhs})"),
            Prim::Lt(k) => format!("(u64)({} < {})", ord(k, lhs), ord(k, rhs)),
            Prim::Le(k) => format!("(u64)({} <= {})", ord(k, lhs), ord(k, rhs)),
            Prim::Compare(k) => {
                let (left, right) = (ord(k, lhs), ord(k, rhs));
                format!("({left} < {right} ? 1ULL : {left} > {right} ? 5ULL : 3ULL)")
            }
            Prim::Fits(from, to) => fits(from, to, lhs),
            Prim::Wrap(_, to) => wrap(to, lhs),
            Prim::ToFloat(from, to) => {
                let v = format!("({})({})", ctype(to), ord(from, lhs));
                return to_float(to, &v);
            }
            Prim::Abs(k) if k.is_signed() => {
                self.check(
                    &format!("(i64){lhs} == {}", signed(k.range().0)),
                    OVERFLOW,
                    at,
                );
                format!("((i64){lhs} < 0 ? (u64)0 - {lhs} : {lhs})")
            }
            Prim::Widen(..) | Prim::Abs(_) => lhs.to_owned(),
            Prim::Min(k) => format!("({} < {} ? {lhs} : {rhs})", ord(k, lhs), ord(k, rhs)),
            Prim::Max(k) => format!("({} > {} ? {lhs} : {rhs})", ord(k, lhs), ord(k, rhs)),
            _ => unreachable!("an integer operation that `int_op` leaves"),
        })
    }
}

/// A C value of float kind `k` as the expression a local takes: an `f64` as it is, and an
/// `f32` in the low bits of a word.
fn to_float(k: NumKind, x: &str) -> Expr {
    if k == NumKind::F32 {
        Expr::word(format!("lt_bits32({x})"))
    } else {
        Expr::double(x.to_owned())
    }
}

/// Whether an integer of kind `from` keeps its value as one of kind `to`.
fn fits(from: NumKind, to: NumKind, v: &str) -> String {
    let (min, max) = to.range();
    let max = max.min(i128::from(i64::MAX));
    let wide = to.bits() == 64;
    match (from.is_signed(), to.is_signed()) {
        (true, true) if wide => "1ULL".to_owned(),
        (true, true) => format!(
            "(u64)((i64){v} >= {} && (i64){v} <= {})",
            signed(min),
            signed(max)
        ),
        (true, false) if wide => format!("(u64)((i64){v} >= 0)"),
        (true, false) => format!("(u64)((i64){v} >= 0 && (i64){v} <= {})", signed(max)),
        (false, _) if wide && !to.is_signed() => "1ULL".to_owned(),
        (false, _) => format!("(u64)({v} <= {:#x}ULL)", u64::try_from(max).unwrap_or(0)),
    }
}

/// An operation on floats of kind `k`, whose operands are C values of the kind's type.
fn float_op(op: Prim, k: NumKind, x: &str, y: &str) -> Expr {
    let f32 = k == NumKind::F32;
    let wide = |v: &str| {
        if f32 {
            format!("(double){v}")
        } else {
            v.to_owned()
        }
    };
    let narrow = |v: String| if f32 { format!("(float)({v})") } else { v };
    let flag = |c: String| Expr::word(format!("(u64)({c})"));
    let suffix = if f32 { "f" } else { "" };
    let value = match op {
        Prim::Add(_) => format!("({x} + {y})"),
        Prim::Sub(_) => format!("({x} - {y})"),
        Prim::Mul(_) => format!("({x} * {y})"),
        Prim::Div(_) => format!("({x} / {y})"),
        Prim::Rem(_) => narrow(format!("stilt_rt_fmod({}, {})", wide(x), wide(y))),
        Prim::Neg(_) => format!("(-{x})"),
        Prim::Eq(_) => return flag(format!("{x} == {y}")),
        Prim::Lt(_) => return flag(format!("{x} < {y}")),
        Prim::Le(_) => return flag(format!("{x} <= {y}")),
        Prim::IsNan(_) => return flag(format!("{x} != {x}")),
        Prim::Compare(_) => {
            return Expr::word(format!("stilt_rt_float_compare({}, {})", wide(x), wide(y)));
        }
        Prim::ToFloat(_, to) => return to_float(to, &format!("({})({x})", ctype(to))),
        Prim::FloatFits(_, to) => return Expr::word(float_fits(to, &wide(x))),
        Prim::FloatToInt(_, to) if to.is_signed() => {
            return Expr::word(format!("lt_to_i64(__builtin_trunc({}))", wide(x)));
        }
        Prim::FloatToInt(..) => {
            return Expr::word(format!("lt_to_u64(__builtin_trunc({}))", wide(x)));
        }
        Prim::Abs(_) => format!("__builtin_fabs{suffix}({x})"),
        Prim::Min(_) => format!("__builtin_elementwise_minimum({x}, {y})"),
        Prim::Max(_) => format!("__builtin_elementwise_maximum({x}, {y})"),
        Prim::Sqrt(_) => format!("__builtin_sqrt{suffix}({x})"),
        Prim::Floor(_) => format!("__builtin_floor{suffix}({x})"),
        Prim::Ceil(_) => format!("__builtin_ceil{suffix}({x})"),
        Prim::Trunc(_) => format!("__builtin_trunc{suffix}({x})"),
        Prim::Round(_) => narrow(format!("stilt_rt_round({})", wide(x))),
        _ => unreachable!("an operation without float operands"),
    };
    to_float(k, &value)
}

/// Whether a float's truncation is a value of kind `to` (numbers.conversions).
fn float_fits(to: NumKind, x: &str) -> String {
    let bits = i32::try_from(to.bits()).unwrap_or(64);
    let (bottom, top) = if to.is_signed() {
        (-(2f64.powi(bits - 1)), 2f64.powi(bits - 1))
    } else {
        (0.0, 2f64.powi(bits))
    };
    format!("(u64)(__builtin_trunc({x}) >= {bottom:?} && __builtin_trunc({x}) < {top:?})")
}
