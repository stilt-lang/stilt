//! The operators on numbers and booleans (numbers.integer-panics, numbers.wrapping and
//! numbers.ieee-754): integers panic on overflow, but for the wrapping operators, and on division
//! by zero; floats follow IEEE 754, an `f32`'s result rounded to `f32`.

use stilt_hir::hir::{BinaryOp, UnaryOp};

use super::{R, panic};
use crate::value::{IntKind, Value};

fn overflow<'a>(k: IntKind) -> R<'a> {
    let name = ["i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64"][usize::from(k.0 % 8)];
    panic("overflow", format!("the result doesn't fit in `{name}`"))
}

fn fitted<'a>(k: IntKind, r: i128) -> R<'a> {
    if k.holds(r) {
        Ok(Value::Int(r, k))
    } else {
        overflow(k)
    }
}

/// The result of a float operation, rounded to `f32` for an `f32`.
pub(crate) fn float<'a>(x: f64, f32: bool) -> Value<'a> {
    #[allow(clippy::cast_possible_truncation)]
    let x = if f32 { f64::from(x as f32) } else { x };
    Value::Float(x, f32)
}

pub(super) fn unary(op: UnaryOp, v: Value<'_>) -> R<'_> {
    match (op, v) {
        (UnaryOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
        (UnaryOp::Not, Value::Int(x, k)) => Ok(Value::Int(k.wrap(!x), k)),
        (UnaryOp::Neg, Value::Int(x, k)) => fitted(k, -x),
        (UnaryOp::Neg, Value::Float(x, f)) => Ok(Value::Float(-x, f)),
        (_, v) => Ok(v),
    }
}

pub(super) fn arithmetic<'a>(op: BinaryOp, lhs: &Value<'a>, rhs: &Value<'a>) -> R<'a> {
    match (lhs, rhs) {
        (Value::Int(a, kind), Value::Int(b, by)) => integer(op, *kind, (*a, *b), *by),
        (Value::Float(a, single), Value::Float(b, _)) => {
            let out = match op {
                BinaryOp::Add => a + b,
                BinaryOp::Sub => a - b,
                BinaryOp::Mul => a * b,
                BinaryOp::Div => a / b,
                _ => a % b,
            };
            Ok(float(out, *single))
        }
        _ => Ok(Value::unit()),
    }
}

fn integer<'a>(op: BinaryOp, k: IntKind, (a, b): (i128, i128), by: IntKind) -> R<'a> {
    match op {
        BinaryOp::Add => fitted(k, a + b),
        BinaryOp::Sub => fitted(k, a - b),
        BinaryOp::Mul => fitted(k, a * b),
        BinaryOp::Div | BinaryOp::Rem if b == 0 => panic("divide-by-zero", "division by zero"),
        BinaryOp::Div => fitted(k, a / b),
        BinaryOp::Rem => fitted(k, a % b),
        BinaryOp::AddWrap => Ok(Value::Int(k.wrap(a + b), k)),
        BinaryOp::SubWrap => Ok(Value::Int(k.wrap(a - b), k)),
        BinaryOp::MulWrap => Ok(Value::Int(k.wrap(a.wrapping_mul(b)), k)),
        BinaryOp::BitAnd => Ok(Value::Int(k.wrap(a & b), k)),
        BinaryOp::BitOr => Ok(Value::Int(k.wrap(a | b), k)),
        BinaryOp::BitXor => Ok(Value::Int(k.wrap(a ^ b), k)),
        BinaryOp::Shl | BinaryOp::Shr => shift(op, k, a, (b, by)),
        _ => Ok(Value::unit()),
    }
}

/// numbers.shifts: a shift by an amount from 0 to the width less one; a left shift drops the
/// bits past the width, and a right shift of a signed value keeps its sign.
fn shift<'a>(op: BinaryOp, k: IntKind, a: i128, (n, by): (i128, IntKind)) -> R<'a> {
    let bits = i128::from(k.bits());
    if n < 0 || n >= bits {
        let name = ["i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64"][usize::from(k.0 % 8)];
        let _ = by;
        return panic(
            "overflow",
            format!("the shift amount {n} is out of range for `{name}`"),
        );
    }
    let n = u32::try_from(n).unwrap_or(0);
    let r = match op {
        BinaryOp::Shl => k.wrap(a << n),
        _ => a >> n,
    };
    Ok(Value::Int(r, k))
}
