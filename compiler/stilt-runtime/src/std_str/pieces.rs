//! The native methods of `str` that std.str-building and std.str-splitting adds to cut and build
//! text: trimming one end, stripping a prefix or a suffix, splitting once, the last match,
//! counting, replacing once, splitting on whitespace and padding.

use super::{s, strings};
use crate::abi::{NONE, Ret, immediate, option};
use crate::text;

/// ASCII whitespace, as `trim` strips it (std.str-splitting).
fn is_space(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\r' | '\x0c')
}

/// Copies of `fill`, the last cut short, that bring `a` to `width` scalar values.
fn padding(a: &str, width: i64, fill: &str) -> String {
    let have = i64::try_from(a.chars().count()).unwrap_or(i64::MAX);
    let missing = usize::try_from(width.saturating_sub(have)).unwrap_or(0);
    if fill.is_empty() {
        return String::new();
    }
    fill.chars().cycle().take(missing).collect()
}

natives! {
    /// `s.trim_start()`: without the ASCII whitespace at its start.
    fn stilt_std_prelude_str_trim_start(a: str) { text::from(a.trim_start_matches(is_space)) }
    /// `s.trim_end()`: without the ASCII whitespace at its end.
    fn stilt_std_prelude_str_trim_end(a: str) { text::from(a.trim_end_matches(is_space)) }
    /// `s.strip_prefix(prefix)`.
    fn stilt_std_prelude_str_strip_prefix(a: str, b: str) {
        option(a.strip_prefix(b).map(text::from))
    }
    /// `s.strip_suffix(suffix)`.
    fn stilt_std_prelude_str_strip_suffix(a: str, b: str) {
        option(a.strip_suffix(b).map(text::from))
    }
    /// `s.rfind(sub)`: the byte offset of the last match, which for `""` is the length.
    fn stilt_std_prelude_str_rfind(a: str, b: str) { option(a.rfind(b).map(|i| i as u64)) }
    /// `s.count(sub)`: the non-overlapping matches, from left to right, of which `""` has one
    /// at every boundary between scalar values and at both ends.
    fn stilt_std_prelude_str_count(a: str, b: str) { a.matches(b).count() as u64 }
    /// `s.replace_first(from, to)`.
    fn stilt_std_prelude_str_replace_first(a: str, b: str, c: str) {
        match a.find(b) {
            Some(i) => text::concat([&a[..i], c, &a[i + b.len()..]].into_iter().map(str::as_bytes)),
            None => text::from(a),
        }
    }
    /// `s.split_whitespace()`: the pieces between runs of ASCII whitespace.
    fn stilt_std_prelude_str_split_whitespace(a: str) {
        strings(a.split_ascii_whitespace().count(), a.split_ascii_whitespace())
    }
    /// `s.pad_start(width, fill)`.
    fn stilt_std_prelude_str_pad_start(a: str, width: int, fill: str) {
        text::from(&format!("{}{a}", padding(a, width as i64, fill)))
    }
    /// `s.pad_end(width, fill)`.
    fn stilt_std_prelude_str_pad_end(a: str, width: int, fill: str) {
        text::from(&format!("{a}{}", padding(a, width as i64, fill)))
    }
}

/// An `Option` of two strings: on `Some`, writes them to `out` and returns the tag, as a native
/// whose result holds a value of several words does (`stilt_runtime::abi`).
///
/// # Safety
///
/// `out` points to room for two words.
unsafe fn pair(parts: Option<(&str, &str)>, out: *mut u64) -> Ret {
    let Some((before, after)) = parts else {
        return NONE;
    };
    // SAFETY: the caller guarantees the room.
    unsafe {
        out.write(text::from(before));
        out.add(1).write(text::from(after));
    }
    Ret::words(immediate(1), 0)
}

/// `s.split_once(sep)`: the text before and after the first occurrence of `sep`.
///
/// # Safety
///
/// `a` and `b` are live strings, and `out` points to room for two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_str_split_once(
    _loc: u64,
    a: u64,
    b: u64,
    out: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    // SAFETY: the caller guarantees the strings and the room.
    unsafe { pair(s(&a).split_once(s(&b)), out) }
}

/// `s.rsplit_once(sep)`: the text before and after the last occurrence of `sep`.
///
/// # Safety
///
/// `a` and `b` are live strings, and `out` points to room for two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_str_rsplit_once(
    _loc: u64,
    a: u64,
    b: u64,
    out: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    // SAFETY: the caller guarantees the strings and the room.
    unsafe { pair(s(&a).rsplit_once(s(&b)), out) }
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_prelude_str_trim_start,
        stilt_std_prelude_str_trim_end,
        stilt_std_prelude_str_strip_prefix,
        stilt_std_prelude_str_strip_suffix,
        stilt_std_prelude_str_split_once,
        stilt_std_prelude_str_rsplit_once,
        stilt_std_prelude_str_rfind,
        stilt_std_prelude_str_count,
        stilt_std_prelude_str_replace_first,
        stilt_std_prelude_str_split_whitespace,
        stilt_std_prelude_str_pad_start,
        stilt_std_prelude_str_pad_end,
    ]
}

#[cfg(test)]
mod tests {
    use super::padding;

    #[test]
    fn padding_cuts_its_last_copy_short() {
        assert_eq!(padding("7", 4, "ab"), "aba");
        assert_eq!(padding("abc", 2, "*"), "");
        assert_eq!(padding("", 3, ""), "");
        assert_eq!(padding("é", 2, "é"), "é");
    }
}
