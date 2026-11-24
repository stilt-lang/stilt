//! The natives of `str` (std.str), on the values of a run: offsets count bytes, and a slice that
//! splits a UTF-8 sequence panics with `utf8-boundary`.

use crate::eval::{R, panic, reserve};
use crate::value::{IntKind, Value};

fn s<'v>(values: &'v [Value<'_>], i: usize) -> &'v str {
    values.get(i).map_or("", Value::as_str)
}

fn strs<'a>(xs: impl IntoIterator<Item = String>) -> Value<'a> {
    Value::list(xs.into_iter().map(Value::str).collect())
}

fn ascii_all(x: &str, f: fn(&u8) -> bool) -> bool {
    !x.is_empty() && x.as_bytes().iter().all(f)
}

/// A text result, weighed as it is made (macros.step-limits).
fn text<'a>(t: String) -> R<'a> {
    reserve(t.len())?;
    Ok(Value::str(t))
}

/// The natives of `str`: its measures, searches and tests, then its other forms.
pub(super) const NAMES: &[&str] = &[
    "len",
    "is_empty",
    "contains",
    "starts_with",
    "ends_with",
    "find",
    "slice",
    "split",
    "lines",
    "trim",
    "replace",
    "chars",
    "bytes",
    "ascii_upper",
    "ascii_lower",
    "join",
    "trim_start",
    "trim_end",
    "strip_prefix",
    "strip_suffix",
    "split_once",
    "rsplit_once",
    "rfind",
    "count",
    "replace_first",
    "split_whitespace",
    "pad_start",
    "pad_end",
    "char_count",
    "reversed",
    "is_ascii",
    "is_ascii_digit",
    "is_ascii_alpha",
    "is_ascii_alphanumeric",
    "is_ascii_whitespace",
    "is_ascii_upper",
    "is_ascii_lower",
    "code_points",
    "from_code_point",
    "from_utf8",
    "from_utf8_lossy",
    "to_i8",
    "to_i16",
    "to_i32",
    "to_i64",
    "to_u8",
    "to_u16",
    "to_u32",
    "to_u64",
    "to_f32",
    "to_f64",
];

pub(super) fn call<'a>(name: &str, values: &[Value<'a>]) -> R<'a> {
    let x = s(values, 0);
    let y = s(values, 1);
    let found = |at: Option<usize>| Value::option(at.map(|i| Value::i64(i as i128)));
    match name {
        "len" => Ok(Value::i64(x.len() as i128)),
        "is_empty" => Ok(Value::Bool(x.is_empty())),
        "contains" => Ok(Value::Bool(x.contains(y))),
        "starts_with" => Ok(Value::Bool(x.starts_with(y))),
        "ends_with" => Ok(Value::Bool(x.ends_with(y))),
        "find" => Ok(found(x.find(y))),
        "rfind" => Ok(found(x.rfind(y))),
        "strip_prefix" => Ok(Value::option(x.strip_prefix(y).map(Value::str))),
        "strip_suffix" => Ok(Value::option(x.strip_suffix(y).map(Value::str))),
        "split_once" => Ok(pair(x.split_once(y))),
        "rsplit_once" => Ok(pair(x.rsplit_once(y))),
        "count" if y.is_empty() => Ok(Value::i64(x.chars().count() as i128 + 1)),
        "count" => Ok(Value::i64(x.matches(y).count() as i128)),
        "char_count" => Ok(Value::i64(x.chars().count() as i128)),
        "is_ascii" => Ok(Value::Bool(x.is_ascii())),
        "is_ascii_digit" => Ok(Value::Bool(ascii_all(x, u8::is_ascii_digit))),
        "is_ascii_alpha" => Ok(Value::Bool(ascii_all(x, u8::is_ascii_alphabetic))),
        "is_ascii_alphanumeric" => Ok(Value::Bool(ascii_all(x, u8::is_ascii_alphanumeric))),
        "is_ascii_whitespace" => Ok(Value::Bool(ascii_all(x, u8::is_ascii_whitespace))),
        "is_ascii_upper" => Ok(Value::Bool(ascii_all(x, u8::is_ascii_uppercase))),
        "is_ascii_lower" => Ok(Value::Bool(ascii_all(x, u8::is_ascii_lowercase))),
        _ => pieces(name, values),
    }
}

/// The natives of `str` that cut it into pieces or list its parts.
fn pieces<'a>(name: &str, values: &[Value<'a>]) -> R<'a> {
    let x = s(values, 0);
    let y = s(values, 1);
    match name {
        "slice" => slice(x, values),
        "split" if y.is_empty() => Ok(strs(x.chars().map(String::from))),
        "split" => Ok(strs(x.split(y).map(String::from))),
        "lines" => Ok(strs(lines(x))),
        "chars" => Ok(strs(x.chars().map(String::from))),
        "bytes" => Ok(Value::list(
            x.bytes()
                .map(|b| Value::Int(i128::from(b), IntKind::U8))
                .collect(),
        )),
        "code_points" => Ok(Value::list(
            x.chars()
                .map(|c| Value::Int(i128::from(u32::from(c)), IntKind::U32))
                .collect(),
        )),
        "split_whitespace" => Ok(strs(
            x.split(|c: char| c.is_ascii_whitespace())
                .filter(|p| !p.is_empty())
                .map(String::from),
        )),
        _ => edits(name, values),
    }
}

/// The natives of `str` that make another text from it.
fn edits<'a>(name: &str, values: &[Value<'a>]) -> R<'a> {
    let x = s(values, 0);
    let y = s(values, 1);
    match name {
        "trim" => text(x.trim_matches(|c: char| c.is_ascii_whitespace()).to_owned()),
        "trim_start" => text(
            x.trim_start_matches(|c: char| c.is_ascii_whitespace())
                .to_owned(),
        ),
        "trim_end" => text(
            x.trim_end_matches(|c: char| c.is_ascii_whitespace())
                .to_owned(),
        ),
        "replace" => {
            // Weighed before it is made, which a long replacement would take beyond the run's
            // memory (macros.step-limits).
            let found = if y.is_empty() {
                x.chars().count() + 1
            } else {
                x.matches(y).count()
            };
            reserve(
                x.len()
                    .saturating_add(found.saturating_mul(s(values, 2).len())),
            )?;
            text(x.replace(y, s(values, 2)))
        }
        "replace_first" => text(x.replacen(y, s(values, 2), 1)),
        "ascii_upper" => text(x.to_ascii_uppercase()),
        "ascii_lower" => text(x.to_ascii_lowercase()),
        "join" => {
            let parts: Vec<&str> = values
                .get(1)
                .map_or(&[][..], Value::as_list)
                .iter()
                .map(Value::as_str)
                .collect();
            let len = parts.iter().map(|p| p.len()).sum::<usize>();
            reserve(len.saturating_add(parts.len().saturating_mul(x.len())))?;
            text(parts.join(x))
        }
        "pad_start" | "pad_end" => pad(name, x, values),
        "reversed" => text(x.chars().rev().collect()),
        _ => Ok(conversions(name, values)),
    }
}

/// The functions of `str` without `self`, and its parsers (numbers.parsing).
fn conversions<'a>(name: &str, values: &[Value<'a>]) -> Value<'a> {
    let x = s(values, 0);
    let bytes = || -> Vec<u8> {
        values
            .first()
            .map_or(&[][..], Value::as_list)
            .iter()
            .map(|b| u8::try_from(b.as_int()).unwrap_or(0))
            .collect()
    };
    match name {
        "from_code_point" => {
            let c = u32::try_from(values.first().map_or(0, Value::as_int))
                .ok()
                .and_then(char::from_u32);
            Value::option(c.map(|c| Value::str(c.to_string())))
        }
        "from_utf8" => Value::option(String::from_utf8(bytes()).ok().map(Value::str)),
        "from_utf8_lossy" => Value::str(String::from_utf8_lossy(&bytes()).into_owned()),
        "to_f32" | "to_f64" => {
            let f32 = name == "to_f32";
            let parsed = decimal_float(x).map(|v| crate::eval::ops_float(v, f32));
            Value::option(parsed)
        }
        _ => match name.strip_prefix("to_").and_then(IntKind::named) {
            Some(k) => {
                let parsed =
                    decimal_int(x).filter(|v| k.holds(*v) && (!x.starts_with('-') || k.signed()));
                Value::option(parsed.map(|v| Value::Int(v, k)))
            }
            None => unreachable!("the table names every native of `str`: {name}"),
        },
    }
}

/// numbers.parsing: an optional `-`, then decimal digits, nothing else.
fn decimal_int(x: &str) -> Option<i128> {
    let digits = x.strip_prefix('-').unwrap_or(x);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) || digits.len() > 30 {
        return None;
    }
    x.parse().ok()
}

/// numbers.parsing: a float as a literal writes it, with an optional `-`.
fn decimal_float(x: &str) -> Option<f64> {
    let body = x.strip_prefix('-').unwrap_or(x);
    let ok = body.bytes().next().is_some_and(|b| b.is_ascii_digit())
        && body
            .bytes()
            .all(|b| b.is_ascii_digit() || matches!(b, b'.' | b'e' | b'E' | b'+' | b'-'));
    if ok { x.parse().ok() } else { None }
}

fn lines(x: &str) -> Vec<String> {
    let mut out: Vec<String> = x
        .split('\n')
        .map(|l| l.strip_suffix('\r').unwrap_or(l).to_owned())
        .collect();
    if x.ends_with('\n') || x.is_empty() {
        out.pop();
    }
    out
}

fn pair<'a>(p: Option<(&str, &str)>) -> Value<'a> {
    Value::option(p.map(|(a, b)| Value::tuple(vec![Value::str(a), Value::str(b)])))
}

fn slice<'a>(x: &str, values: &[Value<'a>]) -> R<'a> {
    let (start, end) = (
        values.get(1).map_or(0, Value::as_int),
        values.get(2).map_or(0, Value::as_int),
    );
    let len = x.len() as i128;
    if start < 0 || start > end || end > len {
        return panic(
            "bounds",
            format!("the range {start}..{end} is out of bounds for a string of length {len}"),
        );
    }
    let (a, b) = (
        usize::try_from(start).unwrap_or(0),
        usize::try_from(end).unwrap_or(0),
    );
    match x.get(a..b) {
        Some(part) => Ok(Value::str(part)),
        None => panic("utf8-boundary", "the range splits a UTF-8 sequence"),
    }
}

fn pad<'a>(name: &str, x: &str, values: &[Value<'a>]) -> R<'a> {
    let width = usize::try_from(values.get(1).map_or(0, Value::as_int)).unwrap_or(0);
    let fill: Vec<char> = s(values, 2).chars().collect();
    let have = x.chars().count();
    if have >= width || fill.is_empty() {
        return Ok(Value::str(x));
    }
    reserve((width - have) * 4)?;
    let padding: String = fill.iter().cycle().take(width - have).collect();
    Ok(Value::str(if name == "pad_start" {
        format!("{padding}{x}")
    } else {
        format!("{x}{padding}")
    }))
}
