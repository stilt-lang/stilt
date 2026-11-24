//! The natives of the integer and float types (numbers.integer-panics and numbers.conversions;
//! std.integers and std.floats), on the values of a run: an integer method panics with `overflow`
//! where its result doesn't fit, and a conversion that may not fit gives an `Option`.

use crate::eval::{R, panic};
use crate::value::{IntKind, Value};

fn int<'a>(x: i128, k: IntKind) -> Value<'a> {
    Value::Int(x, k)
}

fn fitted<'a>(k: IntKind, x: i128) -> R<'a> {
    if k.holds(x) {
        Ok(int(x, k))
    } else {
        let name = ["i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64"][usize::from(k.0 % 8)];
        panic("overflow", format!("the result doesn't fit in `{name}`"))
    }
}

fn arg(values: &[Value<'_>], i: usize) -> i128 {
    values.get(i).map_or(0, Value::as_int)
}

/// The kind a conversion `to_x` or `wrap_to_x` names.
fn target(name: &str) -> Option<IntKind> {
    let t = name
        .strip_prefix("wrap_to_")
        .or_else(|| name.strip_prefix("to_"))?;
    IntKind::named(t)
}

/// A conversion of an integer of kind `k` to kind `t`: the value itself when `t` holds every
/// value of `k`, and otherwise `Some` of it, or `None` when it doesn't fit.
fn converted<'a>(x: i128, k: IntKind, t: IntKind) -> Value<'a> {
    if t.holds(k.min()) && t.holds(k.max()) {
        int(x, t)
    } else {
        Value::option(t.holds(x).then(|| int(x, t)))
    }
}

/// The native `name` of the integer type of kind `k`.
pub(super) fn integer<'a>(k: IntKind, name: &str, values: &[Value<'a>]) -> R<'a> {
    let x = arg(values, 0);
    let y = arg(values, 1);
    let bits = k.bits();
    #[allow(
        clippy::cast_sign_loss,
        reason = "the mask leaves the low bits, never negative"
    )]
    let unsigned = |v: i128| -> u128 { (v & ((1i128 << bits) - 1)) as u128 };
    match name {
        "abs" => fitted(k, x.abs()),
        "min" => Ok(int(x.min(y), k)),
        "max" => Ok(int(x.max(y), k)),
        "to_f32" | "to_f64" => {
            #[allow(clippy::cast_precision_loss)]
            let f = x as f64;
            Ok(crate::eval::ops_float(f, name == "to_f32"))
        }
        _ if name.starts_with("wrap_to_") => {
            let t = target(name).unwrap_or(k);
            Ok(int(t.wrap(x), t))
        }
        _ if name.starts_with("to_") => {
            let t = target(name).unwrap_or(k);
            Ok(converted(x, k, t))
        }
        "checked_add" => Ok(Value::option(k.holds(x + y).then(|| int(x + y, k)))),
        "checked_sub" => Ok(Value::option(k.holds(x - y).then(|| int(x - y, k)))),
        "checked_mul" => {
            let r = x.checked_mul(y).filter(|r| k.holds(*r));
            Ok(Value::option(r.map(|r| int(r, k))))
        }
        "saturating_add" => Ok(int((x + y).clamp(k.min(), k.max()), k)),
        "saturating_sub" => Ok(int((x - y).clamp(k.min(), k.max()), k)),
        "pow" => power(k, x, y),
        "div_euclid" | "rem_euclid" => euclid(k, name, x, y),
        "count_ones" => Ok(Value::i64(i128::from(unsigned(x).count_ones()))),
        "leading_zeros" => {
            let lz = unsigned(x).leading_zeros() - (128 - bits);
            Ok(Value::i64(i128::from(lz)))
        }
        "trailing_zeros" => {
            let tz = if unsigned(x) == 0 {
                bits
            } else {
                unsigned(x).trailing_zeros()
            };
            Ok(Value::i64(i128::from(tz)))
        }
        "gcd" => fitted(k, gcd(x, y)),
        "lcm" if x == 0 || y == 0 => Ok(int(0, k)),
        "lcm" => fitted(k, (x / gcd(x, y) * y).abs()),
        _ => unreachable!("the table names every native of the integer types: {name}"),
    }
}

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn power<'a>(k: IntKind, x: i128, exp: i128) -> R<'a> {
    let mut r: i128 = 1;
    for _ in 0..exp.max(0) {
        r = match r.checked_mul(x) {
            Some(r) if k.holds(r) => r,
            _ => return fitted(k, i128::MAX),
        };
    }
    Ok(int(r, k))
}

fn euclid<'a>(k: IntKind, name: &str, x: i128, y: i128) -> R<'a> {
    if y == 0 {
        return panic("divide-by-zero", "division by zero");
    }
    if name == "div_euclid" {
        fitted(k, x.div_euclid(y))
    } else {
        fitted(k, x.rem_euclid(y))
    }
}

/// The native `name` of `f32`, if `f32`, or of `f64`.
pub(super) fn float<'a>(f32: bool, name: &str, values: &[Value<'a>]) -> R<'a> {
    let x = match values.first() {
        Some(Value::Float(x, _)) => *x,
        _ => 0.0,
    };
    let y = match values.get(1) {
        Some(Value::Float(y, _)) => *y,
        _ => 0.0,
    };
    let rounded = |r: f64| Ok(crate::eval::ops_float(r, f32));
    match name {
        "sqrt" => rounded(x.sqrt()),
        "floor" => rounded(x.floor()),
        "ceil" => rounded(x.ceil()),
        "trunc" => rounded(x.trunc()),
        "round" => rounded(x.round()),
        "abs" => rounded(x.abs()),
        "min" => rounded(extreme(x, y, true)),
        "max" => rounded(extreme(x, y, false)),
        "is_nan" => Ok(Value::Bool(x.is_nan())),
        "to_f32" => Ok(crate::eval::ops_float(x, true)),
        "to_f64" => Ok(Value::Float(x, false)),
        _ if name.starts_with("to_") => {
            let kind = target(name).unwrap_or(IntKind::I64);
            let whole = x.trunc();
            #[allow(clippy::cast_possible_truncation)]
            let fits =
                x.is_finite() && (-1e39..=1e39).contains(&whole) && kind.holds(whole as i128);
            #[allow(clippy::cast_possible_truncation)]
            Ok(Value::option(fits.then(|| int(whole as i128, kind))))
        }
        _ => Ok(math(name, x, y)),
    }
}

/// IEEE 754 `minimum` or `maximum`: NaN if either is, and `-0.0` below `0.0`.
#[allow(clippy::float_cmp, reason = "the language compares floats exactly")]
fn extreme(x: f64, y: f64, least: bool) -> f64 {
    if x.is_nan() || y.is_nan() {
        return f64::NAN;
    }
    let x_first = x < y || (x == y && x.is_sign_negative());
    if x_first == least { x } else { y }
}

/// The natives of `std.math`, on `f64`.
pub(super) fn math<'a>(name: &str, x: f64, y: f64) -> Value<'a> {
    let r = match name {
        "pow" => x.powf(y),
        "exp" => x.exp(),
        "log" => x.ln(),
        "log2" => x.log2(),
        "log10" => x.log10(),
        "sin" => x.sin(),
        "cos" => x.cos(),
        "tan" => x.tan(),
        "asin" => x.asin(),
        "acos" => x.acos(),
        "atan" => x.atan(),
        "atan2" => x.atan2(y),
        "sinh" => x.sinh(),
        "cosh" => x.cosh(),
        "tanh" => x.tanh(),
        "cbrt" => x.cbrt(),
        "hypot" => x.hypot(y),
        _ => unreachable!("the table names every native of `std.math`: {name}"),
    };
    Value::Float(r, false)
}
