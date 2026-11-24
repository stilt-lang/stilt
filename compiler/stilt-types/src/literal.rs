//! Whether number literals fit types (numbers.integer-literals, numbers.float-literals and
//! numbers.negative-literals). The tests are exact: a literal may be longer than any machine
//! integer.

/// A natural number, as little-endian base-2¹⁶ limbs with no trailing zero limb.
type Nat = Vec<u32>;

const BASE: u32 = 1 << 16;

fn normalize(mut n: Nat) -> Nat {
    while n.last() == Some(&0) {
        n.pop();
    }
    n
}

/// `n * m + a`, for small `m` and `a`.
fn mul_add(n: &[u32], m: u32, a: u32) -> Nat {
    let base = u64::from(BASE);
    let mut out = Vec::with_capacity(n.len() + 1);
    let mut carry = u64::from(a);
    for &limb in n {
        let x = u64::from(limb) * u64::from(m) + carry;
        out.push(limb_of(x % base));
        carry = x / base;
    }
    while carry > 0 {
        out.push(limb_of(carry % base));
        carry /= base;
    }
    normalize(out)
}

fn limb_of(x: u64) -> u32 {
    u32::try_from(x).expect("a limb is below 2^16")
}

fn of_digits(radix: u32, digits: &str) -> Nat {
    digits.chars().fold(Vec::new(), |n, c| {
        let d = c
            .to_digit(16)
            .expect("a literal's digits are hexadecimal at most");
        mul_add(&n, radix, d)
    })
}

/// An integer literal's radix and digits, without its prefix and leading zeros.
fn int_digits(text: &str) -> (u32, &str) {
    let (radix, digits) = match text.as_bytes() {
        [b'0', b'x', _, ..] => (16, &text[2..]),
        [b'0', b'o', _, ..] => (8, &text[2..]),
        [b'0', b'b', _, ..] => (2, &text[2..]),
        _ => (10, text),
    };
    (radix, digits.trim_start_matches('0'))
}

/// The value of an integer literal, or `None` when it is surely at least `2^bits`. Every
/// numeric type's values are below 2¹⁰²⁵, so no test needs arithmetic on larger numbers,
/// however long the literal.
fn int_value(text: &str, bits: usize) -> Option<Nat> {
    let (radix, digits) = int_digits(text);
    // A decimal digit adds more than 3 bits, and the first digit at least one.
    let bits_per_digit = match radix {
        16 => 4,
        2 => 1,
        _ => 3,
    };
    if digits.len().saturating_sub(1) * bits_per_digit >= bits {
        None
    } else {
        Some(of_digits(radix, digits))
    }
}

fn compare(a: &[u32], b: &[u32]) -> std::cmp::Ordering {
    a.len()
        .cmp(&b.len())
        .then_with(|| a.iter().rev().cmp(b.iter().rev()))
}

fn pow2(k: usize) -> Nat {
    let mut n = vec![0; k / 16];
    n.push(1 << (k % 16));
    normalize(n)
}

fn add(a: &[u32], b: &[u32]) -> Nat {
    let mut out = Vec::new();
    let mut carry = 0;
    for i in 0..a.len().max(b.len()) {
        let s = a.get(i).unwrap_or(&0) + b.get(i).unwrap_or(&0) + carry;
        out.push(s % BASE);
        carry = s / BASE;
    }
    if carry > 0 {
        out.push(carry);
    }
    normalize(out)
}

fn mul(a: &[u32], b: &[u32]) -> Nat {
    a.iter().rev().fold(Vec::new(), |acc, &limb| {
        let mut shifted = vec![0];
        shifted.extend(acc);
        add(&mul_add(b, limb, 0), &normalize(shifted))
    })
}

/// `a - b`, for `a` at least `b`.
fn sub(a: &[u32], b: &[u32]) -> Nat {
    let mut out = Vec::new();
    let mut borrow = 0;
    for (i, &x) in a.iter().enumerate() {
        let y = b.get(i).copied().unwrap_or(0) + borrow;
        if x < y {
            out.push(x + BASE - y);
            borrow = 1;
        } else {
            out.push(x - y);
            borrow = 0;
        }
    }
    normalize(out)
}

fn pow10(k: usize) -> Nat {
    (0..k).fold(vec![1], |n, _| mul_add(&n, 10, 0))
}

fn bit_length(n: &[u32]) -> usize {
    n.last().map_or(0, |top| {
        (n.len() - 1) * 16 + (32 - top.leading_zeros()) as usize
    })
}

fn trailing_zeros(n: &[u32]) -> usize {
    let zero_limbs = n.iter().take_while(|&&limb| limb == 0).count();
    n.get(zero_limbs)
        .map_or(0, |limb| zero_limbs * 16 + limb.trailing_zeros() as usize)
}

fn width(ty: &str) -> usize {
    match ty {
        "i8" | "u8" => 8,
        "i16" | "u16" => 16,
        "i32" | "u32" => 32,
        "i64" | "u64" => 64,
        _ => unreachable!("`{ty}` is no integer type"),
    }
}

/// Whether the integer literal `text`, negated if `negative`, is a value of the integer type
/// named `ty`.
#[must_use]
pub(crate) fn int_fits(text: &str, negative: bool, ty: &str) -> bool {
    let bits = width(ty);
    let Some(n) = int_value(text, bits + 1) else {
        return false;
    };
    if ty.starts_with('u') {
        n.is_empty() || (!negative && compare(&n, &pow2(bits)).is_lt())
    } else {
        let limit = pow2(bits - 1);
        if negative {
            compare(&n, &limit).is_le()
        } else {
            compare(&n, &limit).is_lt()
        }
    }
}

/// The significand's bits, and the largest power of two below the overflow threshold, of each
/// float type.
fn float_format(ty: &str) -> (usize, usize) {
    match ty {
        "f32" => (24, 128),
        "f64" => (53, 1024),
        _ => unreachable!("`{ty}` is no float type"),
    }
}

/// Whether the float type named `ty` represents the integer literal `text` exactly.
#[must_use]
pub(crate) fn int_exact_in(text: &str, ty: &str) -> bool {
    let (significand, max_exponent) = float_format(ty);
    int_value(text, max_exponent + 1).is_some_and(|n| {
        n.is_empty()
            || (bit_length(&n) - trailing_zeros(&n) <= significand
                && bit_length(&n) <= max_exponent)
    })
}

/// Whether the float literal `text` rounds to a finite value of the float type named `ty`.
///
/// # Panics
///
/// If `ty` isn't a float type.
///
/// A literal `D.D`, `DeE` or `D.DeE` is `m * 10^e` for a natural `m`. It rounds to infinity
/// when it is at least halfway between the largest finite value and the next power of two,
/// `2^max - 2^(max - significand - 1)`.
#[must_use]
pub(crate) fn float_fits(text: &str, ty: &str) -> bool {
    let (significand, max_exponent) = float_format(ty);
    let lower = text.to_ascii_lowercase();
    let (mantissa, exponent) = lower.split_once('e').unwrap_or((&lower, ""));
    let (whole, fraction) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let joined = format!("{whole}{fraction}");
    let digits = joined.trim_start_matches('0');
    let n = i64::try_from(digits.len()).expect("a literal is shorter than 2^63");
    if n == 0 {
        return true;
    }
    let threshold = sub(&pow2(max_exponent), &pow2(max_exponent - significand - 1));
    // The value `digits * 10^e` lies between `10^(n + e - 1)` and `10^(n + e)`. The largest
    // finite value of every float type is below 10^309, so only an `n + e` from 1 to 309 needs
    // a closer look. Then the value is below the threshold, an integer, exactly when its
    // integer part, the first `n + e` digits, is. An exponent too large decides by its sign.
    let written = if exponent.is_empty() { "0" } else { exponent };
    match written.parse::<i64>() {
        Ok(e) if e.abs() <= 1_000_000_000 => {
            let e = e - i64::try_from(fraction.len()).expect("a literal is shorter than 2^63");
            if n + e <= 0 {
                true
            } else if n + e > 309 {
                false
            } else if let Ok(e) = usize::try_from(e) {
                compare(&mul(&of_digits(10, digits), &pow10(e)), &threshold).is_lt()
            } else {
                let kept = usize::try_from(n + e).expect("`n + e` is positive");
                compare(&of_digits(10, &digits[..kept]), &threshold).is_lt()
            }
        }
        _ => exponent.starts_with('-'),
    }
}

/// The form of an integer literal `text`, which may start with `-`, that two literals share
/// exactly when they stand for the same value: `16` and `0x10` do. It is empty for zero.
#[must_use]
pub(crate) fn int_canonical(text: &str) -> String {
    let (negative, text) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    let (radix, digits) = int_digits(text);
    let limbs = of_digits(radix, digits);
    let magnitude = limbs
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(".");
    if negative && !limbs.is_empty() {
        format!("-{magnitude}")
    } else {
        magnitude
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integers_fit_their_ranges() {
        assert!(int_fits("127", false, "i8"));
        assert!(!int_fits("128", false, "i8"));
        assert!(int_fits("128", true, "i8"));
        assert!(!int_fits("129", true, "i8"));
        assert!(int_fits("0xff", false, "u8"));
        assert!(!int_fits("0x100", false, "u8"));
        assert!(!int_fits("1", true, "u8"));
        assert!(int_fits("0", true, "u8"));
        assert!(int_fits("9223372036854775807", false, "i64"));
        assert!(!int_fits("9223372036854775808", false, "i64"));
        assert!(int_fits("18446744073709551615", false, "u64"));
        assert!(!int_fits("1000000000000000000000000000000", false, "u64"));
    }

    #[test]
    fn floats_hold_integers_exactly_or_not() {
        assert!(int_exact_in("16777216", "f32"));
        assert!(!int_exact_in("16777217", "f32"));
        assert!(int_exact_in("9007199254740992", "f64"));
        assert!(!int_exact_in("9007199254740993", "f64"));
    }

    #[test]
    fn floats_overflow_past_their_largest_value() {
        assert!(float_fits("1.0", "f32"));
        assert!(float_fits("3.4e38", "f32"));
        assert!(!float_fits("3.5e38", "f32"));
        assert!(float_fits("1.7976931348623157e308", "f64"));
        assert!(!float_fits("1.8e308", "f64"));
        assert!(float_fits("1e-400", "f64"));
        assert!(float_fits("0.0", "f64"));
    }

    #[test]
    fn equal_literals_share_a_form() {
        assert_eq!(int_canonical("16"), int_canonical("0x10"));
        assert_eq!(int_canonical("0"), "");
        assert_eq!(int_canonical("-0"), "");
        assert_ne!(int_canonical("-1"), int_canonical("1"));
    }
}
