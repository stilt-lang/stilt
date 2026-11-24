//! The text of numbers (numbers.printing-integers and numbers.printing-floats) and of the other
//! primitive values (std.show-output).
//!
//! A number is passed with its *kind*: 0 to 7 for `i8`, `i16`, `i32`, `i64`, `u8`, `u16`,
//! `u32` and `u64`, which the compiler holds sign- or zero-extended to 64 bits, and 8 and 9
//! for `f32` and `f64`, which it holds as their bits.

use crate::text;

pub(crate) const F32: u64 = 8;

/// Whether an integer kind is signed.
pub(crate) const fn signed(kind: u64) -> bool {
    kind < 4
}

/// The decimal text of an integer (numbers.printing-integers).
pub(crate) fn int(kind: u64, value: u64) -> String {
    Digits::new()
        .of(kind, value)
        .iter()
        .map(|&b| char::from(b))
        .collect()
}

/// Room for the decimal text of any integer: a sign and twenty digits.
struct Digits([u8; 21]);

impl Digits {
    const fn new() -> Self {
        Self([0; 21])
    }

    /// The decimal text of an integer of kind `kind`, written from the end of the room.
    fn of(&mut self, kind: u64, value: u64) -> &[u8] {
        let negative = signed(kind) && (value as i64) < 0;
        let mut m = if negative {
            (value as i64).unsigned_abs()
        } else {
            value
        };
        let mut at = self.0.len();
        loop {
            at -= 1;
            self.0[at] = b'0' + (m % 10) as u8;
            m /= 10;
            if m == 0 {
                break;
            }
        }
        if negative {
            at -= 1;
            self.0[at] = b'-';
        }
        &self.0[at..]
    }
}

/// The value of a float word of kind `kind`.
pub(crate) fn float_of(kind: u64, bits: u64) -> f64 {
    if kind == F32 {
        f64::from(f32::from_bits(bits as u32))
    } else {
        f64::from_bits(bits)
    }
}

/// The shortest digits that read back as `x`, a finite nonzero magnitude, in its own format,
/// and the exponent `k` of the form `0.d₁…dₙ × 10^k` (numbers.float-digits).
///
/// Of the candidates of that length, the one nearer `x` wins, and of two as near, the one that
/// rounding `x` to that many digits, half to even, gives, as the reference interpreter finds
/// it.
pub(crate) fn shortest(kind: u64, x: f64) -> (String, i32) {
    // Rust prints the shortest digits that read back as the value, the closest of them to it,
    // but may break a tie between two the other way.
    let scientific = if kind == F32 {
        format!("{:e}", x as f32)
    } else {
        format!("{x:e}")
    };
    let (digits, k) = digits_of(&scientific);
    let rounded = format!("{x:.*e}", digits.len() - 1);
    // `x` is a finite magnitude, so it equals exactly the floats of its bits.
    let reads_back = if kind == F32 {
        rounded
            .parse::<f32>()
            .is_ok_and(|y| f64::from(y).to_bits() == x.to_bits())
    } else {
        rounded
            .parse::<f64>()
            .is_ok_and(|y| y.to_bits() == x.to_bits())
    };
    if reads_back {
        digits_of(&rounded)
    } else {
        (digits, k)
    }
}

/// The digits and the exponent `k` of the form `0.d₁…dₙ × 10^k` of a number in Rust's
/// scientific notation.
fn digits_of(scientific: &str) -> (String, i32) {
    let (mantissa, exponent) = scientific.split_once('e').expect("an exponent");
    let digits: String = mantissa.chars().filter(char::is_ascii_digit).collect();
    let exponent: i32 = exponent.parse().expect("a decimal exponent");
    (digits, exponent + 1)
}

/// The special values, which print the same under every format (numbers.printing-floats;
/// std.format-special-values).
pub(crate) fn special(x: f64) -> Option<&'static str> {
    if x.is_nan() {
        Some("nan")
    } else if x.is_infinite() && x.is_sign_positive() {
        Some("inf")
    } else if x.is_infinite() {
        Some("-inf")
    } else {
        None
    }
}

pub(crate) fn sign(x: f64) -> &'static str {
    if x.is_sign_negative() { "-" } else { "" }
}

/// The text of a float (numbers.printing-floats).
pub(crate) fn float(kind: u64, x: f64) -> String {
    if let Some(s) = special(x) {
        return s.to_owned();
    }
    if x == 0.0 {
        return format!("{}0.0", sign(x));
    }
    let (digits, k) = shortest(kind, x.abs());
    let n = digits.len() as i32;
    let body = if k > -4 && k <= 16 {
        if k <= 0 {
            format!("0.{}{digits}", "0".repeat((-k) as usize))
        } else if n <= k {
            format!("{digits}{}.0", "0".repeat((k - n) as usize))
        } else {
            format!("{}.{}", &digits[..k as usize], &digits[k as usize..])
        }
    } else {
        let (first, rest) = digits.split_at(1);
        let rest = if rest.is_empty() {
            String::new()
        } else {
            format!(".{rest}")
        };
        format!("{first}{rest}e{}", k - 1)
    };
    format!("{}{body}", sign(x))
}

/// The text of an integer of kind `kind`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_show_int(kind: u64, value: u64) -> u64 {
    text::new(Digits::new().of(kind, value))
}

/// The text of a float of kind `kind`, given as its bits.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_show_float(kind: u64, bits: u64) -> u64 {
    text::from(&float(kind, float_of(kind, bits)))
}

/// The text of a `bool`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_show_bool(value: u64) -> u64 {
    text::from(if value == 0 { "false" } else { "true" })
}

/// A string shown nested inside another value: quoted and escaped (std.show-names-and-escapes).
///
/// # Safety
///
/// `s` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_quote(s: u64) -> u64 {
    // SAFETY: the caller guarantees the string is alive.
    text::from(&text::quote(unsafe { text::text(&s) }))
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_rt_show_int,
        stilt_rt_show_float,
        stilt_rt_show_bool,
        stilt_rt_quote,
    ]
}

#[cfg(test)]
mod tests {
    use super::{F32, float, int};

    #[test]
    fn prints_integers_in_decimal() {
        let (i8_kind, i64_kind, u64_kind) = (0, 3, 7);
        assert_eq!(int(i64_kind, 0), "0");
        assert_eq!(int(i64_kind, (-42i64).cast_unsigned()), "-42");
        assert_eq!(
            int(i64_kind, i64::MIN.cast_unsigned()),
            "-9223372036854775808"
        );
        assert_eq!(
            int(i64_kind, i64::MAX.cast_unsigned()),
            "9223372036854775807"
        );
        assert_eq!(int(u64_kind, u64::MAX), "18446744073709551615");
        assert_eq!(int(i8_kind, (-128i64).cast_unsigned()), "-128");
    }

    #[test]
    #[expect(clippy::excessive_precision, reason = "the exact values are the point")]
    fn prints_floats_as_dr_005_shows() {
        let f64_kind = 9;
        for (x, shown) in [
            (1.0, "1.0"),
            (0.1, "0.1"),
            (123_456.789, "123456.789"),
            (0.0001, "0.0001"),
            (0.00001, "1e-5"),
            (1.5e-7, "1.5e-7"),
            (1e16, "1e16"),
            (1e15, "1000000000000000.0"),
            (-0.0, "-0.0"),
            (1_259_266_790_452_956.25, "1259266790452956.2"),
        ] {
            assert_eq!(float(f64_kind, x), shown, "{x}");
        }
        assert_eq!(float(F32, f64::from(0.1f32)), "0.1");
        assert_eq!(float(F32, f64::from(f32::MAX)), "3.4028235e38");
    }

    #[test]
    #[expect(clippy::excessive_precision, reason = "the exact values are the point")]
    fn a_tie_between_two_shortest_candidates_rounds_half_to_even() {
        let f64_kind = 9;
        assert_eq!(
            float(f64_kind, 126.522_003_173_828_125),
            "126.52200317382812"
        );
        assert_eq!(float(f64_kind, 964.565_979_003_906_25), "964.5659790039062");
        assert_eq!(float(F32, 309_978.125), "309978.12");
    }
}
