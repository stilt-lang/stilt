//! The native methods of `str` that std.str-classes and std.code-points adds to classify and
//! convert text: counting and reversing scalar values, the ASCII classes, code points, and strings
//! from code points and bytes.

use super::s;
use crate::abi::{Ret, option};
use crate::object::Header;
use crate::{list, shape, text};

/// Whether `a` isn't empty and every byte passes `test`.
fn all(a: &str, test: fn(&u8) -> bool) -> u64 {
    u64::from(!a.is_empty() && a.bytes().all(|b| test(&b)))
}

/// A new list of the code points of `a`, one `u32` per element.
fn code_points(a: &str) -> u64 {
    let n = a.chars().count();
    let xs = list::new(n, shape::U32);
    // SAFETY: the list is new, with room for `n` elements of four bytes.
    unsafe {
        for (i, c) in a.chars().enumerate() {
            list::at(xs, i).cast::<u32>().write_unaligned(u32::from(c));
        }
        list::set_len(xs, n);
    }
    xs as u64
}

natives! {
    /// `s.char_count()`: the number of Unicode scalar values.
    fn stilt_std_prelude_str_char_count(a: str) { a.chars().count() as u64 }
    /// `s.reversed()`: the scalar values in reverse order.
    fn stilt_std_prelude_str_reversed(a: str) { text::from(&a.chars().rev().collect::<String>()) }
    /// `s.is_ascii()`.
    fn stilt_std_prelude_str_is_ascii(a: str) { u64::from(a.is_ascii()) }
    /// `s.is_ascii_digit()`.
    fn stilt_std_prelude_str_is_ascii_digit(a: str) { all(a, u8::is_ascii_digit) }
    /// `s.is_ascii_alpha()`.
    fn stilt_std_prelude_str_is_ascii_alpha(a: str) { all(a, u8::is_ascii_alphabetic) }
    /// `s.is_ascii_alphanumeric()`.
    fn stilt_std_prelude_str_is_ascii_alphanumeric(a: str) { all(a, u8::is_ascii_alphanumeric) }
    /// `s.is_ascii_whitespace()`: space, `\t`, `\n`, `\r` and form feed.
    fn stilt_std_prelude_str_is_ascii_whitespace(a: str) { all(a, u8::is_ascii_whitespace) }
    /// `s.is_ascii_upper()`.
    fn stilt_std_prelude_str_is_ascii_upper(a: str) { all(a, u8::is_ascii_uppercase) }
    /// `s.is_ascii_lower()`.
    fn stilt_std_prelude_str_is_ascii_lower(a: str) { all(a, u8::is_ascii_lowercase) }
    /// `s.code_points()`.
    fn stilt_std_prelude_str_code_points(a: str) { code_points(a) }
    /// `str.from_code_point(point)`, `None` for a surrogate or a value above `0x10FFFF`.
    fn stilt_std_prelude_str_from_code_point(c: int) {
        let mut buffer = [0; 4];
        option(char::from_u32(c as u32).map(|c| text::from(c.encode_utf8(&mut buffer))))
    }
    /// `str.from_utf8(bytes)`.
    fn stilt_std_prelude_str_from_utf8(bytes: int) {
        // SAFETY: the native's caller guarantees a live list of `u8`.
        let bytes = unsafe { list::as_bytes(bytes as *mut Header) };
        option(std::str::from_utf8(bytes).ok().map(text::from))
    }
    /// `str.from_utf8_lossy(bytes)`: each maximal subpart of an invalid sequence becomes
    /// U+FFFD, as the Unicode Standard recommends (§3.9).
    fn stilt_std_prelude_str_from_utf8_lossy(bytes: int) {
        // SAFETY: the native's caller guarantees a live list of `u8`.
        let bytes = unsafe { list::as_bytes(bytes as *mut Header) };
        text::from(&String::from_utf8_lossy(bytes))
    }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_prelude_str_char_count,
        stilt_std_prelude_str_reversed,
        stilt_std_prelude_str_is_ascii,
        stilt_std_prelude_str_is_ascii_digit,
        stilt_std_prelude_str_is_ascii_alpha,
        stilt_std_prelude_str_is_ascii_alphanumeric,
        stilt_std_prelude_str_is_ascii_whitespace,
        stilt_std_prelude_str_is_ascii_upper,
        stilt_std_prelude_str_is_ascii_lower,
        stilt_std_prelude_str_code_points,
        stilt_std_prelude_str_from_code_point,
        stilt_std_prelude_str_from_utf8,
        stilt_std_prelude_str_from_utf8_lossy,
    ]
}
