//! The natives of `std.meta` that read text (meta.shapes): `n.parse(text)` of an integer
//! type's `meta.Integer`, which gives `Some` only for exactly the text that `n.text` writes. The
//! other accessors compile inline, reading the descriptors that `stilt_mir` lays out.
//!
//! An integer's kind is as `crate::show` numbers it, and its value is held sign- or
//! zero-extended to 64 bits.

use crate::show::signed;
use crate::text;

/// The range of an integer kind.
fn range(kind: u64) -> (i128, i128) {
    match kind {
        0 => (i8::MIN.into(), i8::MAX.into()),
        1 => (i16::MIN.into(), i16::MAX.into()),
        2 => (i32::MIN.into(), i32::MAX.into()),
        3 => (i64::MIN.into(), i64::MAX.into()),
        4 => (0, u8::MAX.into()),
        5 => (0, u16::MAX.into()),
        6 => (0, u32::MAX.into()),
        _ => (0, u64::MAX.into()),
    }
}

/// The integer of kind `kind` whose decimal text is exactly `text`: digits with no leading
/// zero, after a `-` for a negative one, and in the kind's range.
fn parsed(kind: u64, text: &[u8]) -> Option<u64> {
    let (negative, digits) = match text.split_first() {
        Some((b'-', rest)) => (true, rest),
        _ => (false, text),
    };
    if digits.is_empty() || !digits.iter().all(u8::is_ascii_digit) {
        return None;
    }
    if digits[0] == b'0' && (digits.len() > 1 || negative) {
        return None;
    }
    let value: i128 = std::str::from_utf8(text).ok()?.parse().ok()?;
    let (min, max) = range(kind);
    if !(min..=max).contains(&value) {
        return None;
    }
    #[expect(
        clippy::cast_possible_truncation,
        reason = "the value is in the kind's range"
    )]
    Some(if signed(kind) {
        value as i64 as u64
    } else {
        value as u64
    })
}

/// Whether `text` is exactly the decimal text of an integer of kind `kind`.
///
/// # Safety
///
/// `text` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_int_valid(kind: u64, text: u64) -> u64 {
    // SAFETY: the caller guarantees the string is alive.
    u64::from(parsed(kind, unsafe { text::bytes(&text) }).is_some())
}

/// The integer of kind `kind` whose decimal text is `text`, which `stilt_rt_int_valid` said
/// it is.
///
/// # Safety
///
/// `text` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_int_parse(kind: u64, text: u64) -> u64 {
    // SAFETY: the caller guarantees the string is alive.
    parsed(kind, unsafe { text::bytes(&text) }).unwrap_or(0)
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![stilt_rt_int_valid, stilt_rt_int_parse,]
}

#[cfg(test)]
mod tests {
    use super::parsed;

    #[test]
    fn only_the_text_that_text_writes() {
        assert_eq!(parsed(4, b"255"), Some(255));
        assert_eq!(parsed(4, b"256"), None);
        assert_eq!(parsed(3, b"-42"), Some((-42i64) as u64));
        assert_eq!(parsed(3, b"0"), Some(0));
        for text in ["-0", "+5", "05", " 5", "5 ", "", "-", "1e3"] {
            assert_eq!(parsed(3, text.as_bytes()), None, "{text}");
        }
        assert_eq!(parsed(4, b"-1"), None);
        assert_eq!(parsed(0, b"-128"), Some((-128i64) as u64));
    }
}
