//! The native methods of `str` (std.str), and the parsing of numbers (numbers.parsing, rule
//! 18).
//!
//! Lengths and offsets count bytes (std.bytes-and-scalars). Every method borrows its strings and
//! returns a new value.

use crate::abi::{Ret, option};
use crate::object::Header;
use crate::{list, panic, shape, text};

/// The text of a live string.
///
/// # Safety
///
/// `s` holds a live string, which outlives the text.
unsafe fn s(s: &u64) -> &str {
    // SAFETY: the caller guarantees the string is alive.
    unsafe { text::text(s) }
}

/// A list of new strings, with room for `n` of them, the most there are.
fn strings<'a>(n: usize, pieces: impl IntoIterator<Item = &'a str>) -> u64 {
    let xs = list::new(n, shape::STR);
    for piece in pieces {
        // SAFETY: the list is new, so nothing else references it, and holds strings.
        unsafe { list::push_word(xs, text::from(piece)) };
    }
    xs as u64
}

/// Defines natives of `str` that borrow their strings and can't fail, each of whose bodies
/// gives the one word of its result or a [`Ret`] of two.
macro_rules! natives {
    ($($(#[$doc:meta])* fn $name:ident($($arg:ident: $kind:ident),*) $body:block)*) => {
        $(
            $(#[$doc])*
            ///
            /// # Safety
            ///
            /// Every string argument is a live string.
            #[unsafe(no_mangle)]
            pub(crate) unsafe extern "C" fn $name(_loc: u64, $($arg: u64),*) -> Ret {
                $(let $arg = natives!(@arg $kind $arg);)*
                Ret::from($body)
            }
        )*
    };
    (@arg str $arg:ident) => {
        // SAFETY: the native's caller guarantees its string arguments are alive.
        unsafe { s(&$arg) }
    };
    (@arg int $arg:ident) => { $arg };
    (@arg word $arg:ident) => { $arg };
}

mod classes;
mod pieces;
#[cfg(test)]
mod tests;

natives! {
    /// `s.len()`: its length in bytes.
    fn stilt_std_prelude_str_len(a: str) { a.len() as u64 }
    /// `s.is_empty()`.
    fn stilt_std_prelude_str_is_empty(a: str) { u64::from(a.is_empty()) }
    /// `s.contains(sub)`.
    fn stilt_std_prelude_str_contains(a: str, b: str) { u64::from(a.contains(b)) }
    /// `s.starts_with(prefix)`.
    fn stilt_std_prelude_str_starts_with(a: str, b: str) { u64::from(a.starts_with(b)) }
    /// `s.ends_with(suffix)`.
    fn stilt_std_prelude_str_ends_with(a: str, b: str) { u64::from(a.ends_with(b)) }
    /// `s.find(sub)`: the byte offset of the first match.
    fn stilt_std_prelude_str_find(a: str, b: str) { option(a.find(b).map(|i| i as u64)) }
    /// `s.split(sep)`: the pieces between the occurrences of `sep`, or the scalar values when
    /// it is empty.
    fn stilt_std_prelude_str_split(a: str, b: str) { split(a, b) }
    /// `s.lines()`: the pieces between the `\n`s, each without one trailing `\r`, and no empty
    /// last line after a final newline.
    fn stilt_std_prelude_str_lines(a: str) {
        let pieces = lines(a);
        strings(pieces.len(), pieces)
    }
    /// `s.trim()`: without the ASCII whitespace at either end.
    fn stilt_std_prelude_str_trim(a: str) {
        text::from(a.trim_matches(|c| matches!(c, ' ' | '\t' | '\n' | '\r' | '\x0c')))
    }
    /// `s.replace(from, to)`: each occurrence replaced, left to right, or `to` at every
    /// boundary between scalar values, and at both ends, when `from` is empty.
    fn stilt_std_prelude_str_replace(a: word, b: str, c: str) { replace(a, b, c) }
    /// `s.chars()`: one string per Unicode scalar value.
    fn stilt_std_prelude_str_chars(a: str) { chars(a) }
    /// `s.bytes()`.
    fn stilt_std_prelude_str_bytes(a: str) { bytes(a) }
    /// `s.ascii_upper()`.
    fn stilt_std_prelude_str_ascii_upper(a: str) { cased(a, <[u8]>::make_ascii_uppercase) }
    /// `s.ascii_lower()`.
    fn stilt_std_prelude_str_ascii_lower(a: str) { cased(a, <[u8]>::make_ascii_lowercase) }
    /// `sep.join(parts)`: the parts with `sep` between them.
    fn stilt_std_prelude_str_join(a: str, parts: word) { join(a, parts) }
    /// `s.to_i8()`, and the other integer parsers.
    fn stilt_std_prelude_str_to_i8(a: str) { option(parse_int(a, 8, true)) }
    fn stilt_std_prelude_str_to_i16(a: str) { option(parse_int(a, 16, true)) }
    fn stilt_std_prelude_str_to_i32(a: str) { option(parse_int(a, 32, true)) }
    fn stilt_std_prelude_str_to_i64(a: str) { option(parse_int(a, 64, true)) }
    fn stilt_std_prelude_str_to_u8(a: str) { option(parse_int(a, 8, false)) }
    fn stilt_std_prelude_str_to_u16(a: str) { option(parse_int(a, 16, false)) }
    fn stilt_std_prelude_str_to_u32(a: str) { option(parse_int(a, 32, false)) }
    fn stilt_std_prelude_str_to_u64(a: str) { option(parse_int(a, 64, false)) }
    /// `s.to_f32()`.
    fn stilt_std_prelude_str_to_f32(a: str) {
        let x = valid_float(a).then(|| a.parse::<f32>().ok()).flatten();
        option(x.filter(|x| x.is_finite()).map(|x| u64::from(x.to_bits())))
    }
    /// `s.to_f64()`.
    fn stilt_std_prelude_str_to_f64(a: str) {
        let x = valid_float(a).then(|| a.parse::<f64>().ok()).flatten();
        option(x.filter(|x| x.is_finite()).map(f64::to_bits))
    }
}

fn chars(a: &str) -> u64 {
    let mut buffer = [0; 4];
    let xs = list::new(a.chars().count(), shape::STR);
    for c in a.chars() {
        // SAFETY: the list is new, so nothing else references it, and holds strings.
        unsafe { list::push_word(xs, text::from(c.encode_utf8(&mut buffer))) };
    }
    xs as u64
}

/// The pieces of `a` between the occurrences of `sep`, which isn't empty: those of a
/// separator of one byte found as a character, which searches faster.
fn split(a: &str, sep: &str) -> u64 {
    match sep.as_bytes() {
        [] => chars(a),
        &[b] => {
            let n = a.bytes().filter(|&x| x == b).count() + 1;
            strings(n, a.split(char::from(b)))
        }
        _ => strings(a.matches(sep).count() + 1, a.split(sep)),
    }
}

/// The string `word` with each occurrence of `from` replaced by `to`, written once, or the
/// string itself when `from` doesn't occur.
fn replace(word: u64, from: &str, to: &str) -> u64 {
    // SAFETY: the caller of the native guarantees the string is alive.
    let a = unsafe { s(&word) };
    if from.is_empty() {
        return text::from(&a.replace(from, to));
    }
    let starts: Vec<usize> = a.match_indices(from).map(|(i, _)| i).collect();
    if starts.is_empty() {
        // SAFETY: as above; the result takes a reference of its own.
        unsafe { crate::object::dup(word) };
        return word;
    }
    let kept = a.len() - starts.len() * from.len();
    let len = (starts.len().checked_mul(to.len()))
        .and_then(|added| added.checked_add(kept))
        .unwrap_or_else(|| crate::entry::fatal("out of memory"));
    let mut out = text::Builder::new(len);
    let mut last = 0;
    for i in starts {
        out.push(&a.as_bytes()[last..i]);
        out.push(to.as_bytes());
        last = i + from.len();
    }
    out.push(&a.as_bytes()[last..]);
    out.finish()
}

/// `a` with its ASCII letters changed by `change`.
fn cased(a: &str, change: fn(&mut [u8])) -> u64 {
    let mut out = text::Builder::new(a.len());
    out.push(a.as_bytes());
    change(out.written_mut());
    out.finish()
}

/// A list of the bytes of `a`, one byte per element.
fn bytes(a: &str) -> u64 {
    list::of_bytes(a.as_bytes()) as u64
}

fn lines(a: &str) -> Vec<&str> {
    let mut pieces: Vec<&str> = a.split('\n').collect();
    if pieces.last() == Some(&"") {
        pieces.pop();
    }
    pieces
        .into_iter()
        .map(|line| line.strip_suffix('\r').unwrap_or(line))
        .collect()
}

/// The parts with `sep` between them, or the one part itself.
fn join(sep: &str, parts: u64) -> u64 {
    // SAFETY: the caller of the native guarantees `parts` is a live list of live strings.
    let parts = unsafe { list::words(parts as *mut Header) };
    if let &[part] = parts {
        // SAFETY: as above; the result takes a reference of its own.
        unsafe { crate::object::dup(part) };
        return part;
    }
    // SAFETY: as above.
    let len: usize = parts.iter().map(|&p| unsafe { text::len(p) }).sum();
    let mut out = text::Builder::new(len + sep.len() * parts.len().saturating_sub(1));
    for (i, p) in parts.iter().enumerate() {
        if i > 0 {
            out.push(sep.as_bytes());
        }
        // SAFETY: as above.
        out.push(unsafe { text::bytes(p) });
    }
    out.finish()
}

/// An integer of `bits` bits, signed or not, as the whole of `a` writes it: `-?[0-9]+`, which
/// a type without negative values doesn't accept with a `-` (numbers.parsing).
fn parse_int(a: &str, bits: u32, signed: bool) -> Option<u64> {
    let (negative, digits) = match a.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, a),
    };
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) || negative && !signed {
        return None;
    }
    let mut m: u64 = 0;
    for b in digits.bytes() {
        m = m.checked_mul(10)?.checked_add(u64::from(b - b'0'))?;
    }
    let m = i128::from(m);
    let value = if negative { -m } else { m };
    let (min, max) = if signed {
        (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
    } else {
        (0, (1i128 << bits) - 1)
    };
    (min <= value && value <= max).then_some(value as i64 as u64)
}

/// Whether the whole of `a` is a float as numbers.parsing writes it:
/// `-?[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?`.
fn valid_float(a: &str) -> bool {
    let b = a.as_bytes();
    let mut i = usize::from(b.first() == Some(&b'-'));
    let digits = |i: &mut usize| {
        let start = *i;
        while *i < b.len() && b[*i].is_ascii_digit() {
            *i += 1;
        }
        *i > start
    };
    if !digits(&mut i) {
        return false;
    }
    if i < b.len() && b[i] == b'.' {
        i += 1;
        if !digits(&mut i) {
            return false;
        }
    }
    if i < b.len() && (b[i] == b'e' || b[i] == b'E') {
        i += 1;
        if i < b.len() && (b[i] == b'+' || b[i] == b'-') {
            i += 1;
        }
        if !digits(&mut i) {
            return false;
        }
    }
    i == b.len()
}

/// `s.slice(start, end)`: bytes `start` up to `end`, or a panic with `bounds` unless
/// `0 ≤ start ≤ end ≤ len`, or with `utf8-boundary` when an offset falls inside a UTF-8
/// sequence.
///
/// # Safety
///
/// `a` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_str_slice(
    loc: u64,
    a: u64,
    start: i64,
    end: i64,
) -> Ret {
    // SAFETY: the caller guarantees the string is alive.
    let a = unsafe { s(&a) };
    let len = a.len();
    let range = usize::try_from(start)
        .ok()
        .zip(usize::try_from(end).ok())
        .filter(|&(s, e)| s <= e && e <= len);
    let Some((s, e)) = range else {
        panic::panic(
            loc,
            panic::BOUNDS,
            &format!("the range {start}..{end} is out of bounds for a string of {len} bytes"),
        )
    };
    if !a.is_char_boundary(s) || !a.is_char_boundary(e) {
        panic::panic(
            loc,
            panic::UTF8_BOUNDARY,
            &format!("the range {start}..{end} splits a UTF-8 sequence"),
        );
    }
    Ret::ok(text::from(&a[s..e]))
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    let own = crate::exports![
        stilt_std_prelude_str_len,
        stilt_std_prelude_str_is_empty,
        stilt_std_prelude_str_contains,
        stilt_std_prelude_str_starts_with,
        stilt_std_prelude_str_ends_with,
        stilt_std_prelude_str_find,
        stilt_std_prelude_str_slice,
        stilt_std_prelude_str_split,
        stilt_std_prelude_str_lines,
        stilt_std_prelude_str_trim,
        stilt_std_prelude_str_replace,
        stilt_std_prelude_str_chars,
        stilt_std_prelude_str_bytes,
        stilt_std_prelude_str_ascii_upper,
        stilt_std_prelude_str_ascii_lower,
        stilt_std_prelude_str_join,
        stilt_std_prelude_str_to_i8,
        stilt_std_prelude_str_to_i16,
        stilt_std_prelude_str_to_i32,
        stilt_std_prelude_str_to_i64,
        stilt_std_prelude_str_to_u8,
        stilt_std_prelude_str_to_u16,
        stilt_std_prelude_str_to_u32,
        stilt_std_prelude_str_to_u64,
        stilt_std_prelude_str_to_f32,
        stilt_std_prelude_str_to_f64,
    ];
    [own, pieces::symbols(), classes::symbols()].concat()
}
