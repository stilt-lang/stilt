//! Format specs (std.width-fill-and-alignment, std.precision, std.integer-kinds,
//! std.scientific-notation and std.format-special-values): the text of a splice whose spec gives it
//! a kind, a precision or a width.
//!
//! The compiler passes a spec as two words: the fill, the alignment and the kind in the first,
//! as `fill << 16 | align << 8 | kind`, where an alignment or a kind of 0 is none; and the
//! width and the precision in the second, as `width << 32 | precision`, where a precision of
//! `0xffff_ffff` is none.

use crate::show::{self, F32, float_of, shortest, sign, special};
use crate::text;

/// A spec's kind for a value that is no number, whose text the caller passes.
const NOT_A_NUMBER: u64 = 255;
const NO_PRECISION: u64 = 0xffff_ffff;

struct Spec {
    fill: char,
    align: u8,
    kind: u8,
    width: usize,
    precision: Option<usize>,
}

impl Spec {
    fn of(first: u64, second: u64) -> Self {
        let precision = second & 0xffff_ffff;
        Spec {
            fill: char::from_u32((first >> 16) as u32).unwrap_or(' '),
            align: (first >> 8 & 0xff) as u8,
            kind: (first & 0xff) as u8,
            width: usize::try_from(second >> 32).unwrap_or(0),
            precision: (precision != NO_PRECISION).then(|| usize::try_from(precision).unwrap_or(0)),
        }
    }
}

/// A splice formatted by its spec. `kind` is the kind of a number `value`, as `show` numbers
/// them, or 255 for a value whose text is the string `shown`.
///
/// # Safety
///
/// `shown` is a live string when `kind` is 255.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_format(
    kind: u64,
    value: u64,
    shown: u64,
    first: u64,
    second: u64,
) -> u64 {
    let shown = if kind == NOT_A_NUMBER {
        // SAFETY: the caller guarantees the text is a live string.
        unsafe { text::text(&shown) }
    } else {
        ""
    };
    text::from(&formatted(kind, value, shown, first, second))
}

/// A splice formatted by its spec, as [`stilt_rt_format`] gives it, of a number `value` of
/// kind `kind`, or of the text `shown` when `kind` is 255.
pub(crate) fn formatted(kind: u64, value: u64, shown: &str, first: u64, second: u64) -> String {
    let spec = Spec::of(first, second);
    let body = if kind == NOT_A_NUMBER {
        shown.to_owned()
    } else if kind >= F32 {
        float(&spec, kind, float_of(kind, value))
    } else {
        int(&spec, kind, value)
    };
    pad(&spec, kind != NOT_A_NUMBER, &body)
}

/// std.integer-kinds: an integer in hexadecimal, octal or binary, a negative one as its two's
/// complement at its type's width, and otherwise in decimal.
fn int(spec: &Spec, kind: u64, value: u64) -> String {
    let bits = [8, 16, 32, 64][usize::try_from(kind % 4).unwrap_or(3)];
    let m = if bits == 64 {
        value
    } else {
        value & ((1 << bits) - 1)
    };
    match spec.kind {
        b'x' => format!("{m:x}"),
        b'X' => format!("{m:X}"),
        b'o' => format!("{m:o}"),
        b'b' => format!("{m:b}"),
        _ => show::int(kind, value),
    }
}

/// std.precision, std.scientific-notation and std.format-special-values: a float in scientific or
/// fixed notation, or as `show` prints it.
fn float(spec: &Spec, kind: u64, x: f64) -> String {
    match (spec.kind, spec.precision) {
        (b'e', precision) => scientific(kind, precision, x),
        (_, Some(precision)) => match special(x) {
            Some(s) => s.to_owned(),
            None => format!("{x:.precision$}"),
        },
        _ => show::float(kind, x),
    }
}

/// std.scientific-notation: the form `d.ddde±k` of numbers.float-notation, with the shortest digits
/// or exactly `precision` of them after the point, rounding the exact value half to even.
fn scientific(kind: u64, precision: Option<usize>, x: f64) -> String {
    if let Some(s) = special(x) {
        return s.to_owned();
    }
    match precision {
        Some(p) => format!("{x:.p$e}"),
        None if x == 0.0 => format!("{}0e0", sign(x)),
        None => {
            let (digits, k) = shortest(kind, x.abs());
            let (first, rest) = digits.split_at(1);
            let point = if rest.is_empty() {
                String::new()
            } else {
                format!(".{rest}")
            };
            format!("{}{first}{point}e{}", sign(x), k - 1)
        }
    }
}

/// std.width-fill-and-alignment: the text padded to the spec's width, counted in Unicode scalar
/// values. Numbers align right and everything else left, unless the spec says, and centred text
/// puts the extra fill on the right.
fn pad(spec: &Spec, number: bool, body: &str) -> String {
    let pad = spec.width.saturating_sub(body.chars().count());
    if pad == 0 {
        return body.to_owned();
    }
    let fill = |n: usize| std::iter::repeat_n(spec.fill, n).collect::<String>();
    let align = match spec.align {
        0 if number => b'>',
        0 => b'<',
        a => a,
    };
    match align {
        b'>' => format!("{}{body}", fill(pad)),
        b'^' => format!("{}{body}{}", fill(pad / 2), fill(pad - pad / 2)),
        _ => format!("{body}{}", fill(pad)),
    }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![stilt_rt_format,]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spec(kind: u8, width: usize, precision: Option<usize>) -> Spec {
        Spec {
            fill: '*',
            align: 0,
            kind,
            width,
            precision,
        }
    }

    #[test]
    fn integers_in_other_bases_show_their_twos_complement() {
        assert_eq!(int(&spec(b'x', 0, None), 3, u64::MAX), "ffffffffffffffff");
        assert_eq!(int(&spec(b'x', 0, None), 0, u64::MAX), "ff");
        assert_eq!(int(&spec(b'b', 0, None), 3, 0), "0");
        assert_eq!(int(&spec(b'X', 0, None), 7, 255), "FF");
    }

    #[test]
    fn precision_rounds_the_exact_value_half_to_even() {
        assert_eq!(float(&spec(0, 0, Some(2)), 9, -0.001), "-0.00");
        assert_eq!(float(&spec(0, 0, Some(0)), 9, 2.5), "2");
        assert_eq!(float(&spec(b'e', 0, Some(2)), 9, 12345.0), "1.23e4");
        assert_eq!(float(&spec(b'e', 0, None), 9, -0.0), "-0e0");
        assert_eq!(float(&spec(b'e', 0, Some(1)), 9, 0.0), "0.0e0");
        assert_eq!(float(&spec(b'e', 0, None), 9, 1500.0), "1.5e3");
    }

    #[test]
    fn centred_text_puts_the_extra_fill_on_the_right() {
        let mut s = spec(0, 4, None);
        s.align = b'^';
        assert_eq!(pad(&s, true, "7"), "*7**");
        assert_eq!(pad(&spec(0, 3, None), true, "7"), "**7");
        assert_eq!(pad(&spec(0, 3, None), false, "é"), "é**");
    }
}
