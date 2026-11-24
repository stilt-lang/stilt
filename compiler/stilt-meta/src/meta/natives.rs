//! The natives of `std.meta` that macros use (macros.tokens-and-code). Each performs nothing but
//! the allocation of what it makes.

use std::sync::Arc;

use stilt_hir::hir::CodeForm;
use stilt_hir::procs::{Origin, Rel};
use stilt_syntax::SyntaxKind;

use crate::eval::{Flow, Machine, R, panic};
use crate::run::Io;
use crate::value::{ErrorValue, Meta, NameValue, Span, Text, TextOrigin, Value};

/// Where a token made from a text is placed, as the user's: at its place in the use's file,
/// or at the literal that names the file it is in (macros.errors-in-expansions).
pub(crate) fn placed(io: &Io<'_>, span: Span) -> Origin {
    match span.file {
        Some(k) => Origin::Placed {
            at: io.literal_of(k),
            user: true,
        },
        None => Origin::Placed {
            at: Rel {
                start: span.start,
                end: span.end,
            },
            user: true,
        },
    }
}

/// The source of the value's bytes from `a` to `b`, widened to whole escapes.
pub(crate) fn text_span(io: &Io<'_>, x: &Text, a: usize, b: usize) -> Span {
    let _ = io;
    match &x.origin {
        TextOrigin::File(k) => Span {
            start: offset(a),
            end: offset(b),
            file: Some(*k),
        },
        TextOrigin::Literal { raw, at } => {
            let map = raw_offsets(raw);
            let start = map.get(a).map_or(raw.len(), |r| r.0);
            let end = if b > a {
                map.get(b - 1).map_or(raw.len(), |r| r.1)
            } else {
                start
            };
            Span {
                start: at.start + offset(start),
                end: at.start + offset(end),
                file: at.file,
            }
        }
    }
}

fn offset(x: usize) -> i64 {
    i64::try_from(x).unwrap_or(i64::MAX)
}

/// For each byte of a literal's value, the raw offsets of the escape or character that writes
/// it.
fn raw_offsets(raw: &str) -> Vec<(usize, usize)> {
    let bytes = raw.as_bytes();
    let end = if raw.len() > 1 && raw.ends_with('"') {
        raw.len() - 1
    } else {
        raw.len()
    };
    let mut out = Vec::new();
    let mut i = usize::from(raw.starts_with('"'));
    while i < end {
        let (len, value_len) = if bytes[i] == b'\\' {
            escape(&raw[i..end])
        } else {
            let c = raw[i..].chars().next().map_or(1, char::len_utf8);
            (c, c)
        };
        for _ in 0..value_len {
            out.push((i, i + len));
        }
        i += len.max(1);
    }
    out
}

/// The length of the escape at the start of `rest`, and of the bytes it writes.
fn escape(rest: &str) -> (usize, usize) {
    match rest.as_bytes().get(1) {
        Some(b'u') => {
            let close = rest.find('}').map_or(rest.len(), |c| c + 1);
            let value = rest
                .get(3..close.saturating_sub(1))
                .and_then(|h| u32::from_str_radix(h, 16).ok())
                .and_then(char::from_u32)
                .map_or(1, char::len_utf8);
            (close, value)
        }
        Some(_) => (2, 1),
        None => (1, 1),
    }
}

/// The method `name` of the native type `owner` of `std.meta`.
pub(crate) fn member<'a>(
    mach: &mut Machine<'a>,
    owner: &str,
    name: &str,
    values: &mut [Value<'a>],
) -> R<'a> {
    let meta = |i: usize| values.get(i).and_then(Value::as_meta).cloned();
    match (owner, name, meta(0)) {
        ("Span", "to", Some(Meta::Span(from))) => match meta(1) {
            Some(Meta::Span(upto)) => Ok(Value::meta(Meta::Span(from.to(upto)))),
            _ => Ok(Value::meta(Meta::Span(from))),
        },
        ("Token", "kind", Some(Meta::Token(tok))) => Ok(super::tokens::kind_value(&tok.kind)),
        ("Token", "span", Some(Meta::Token(tok))) => Ok(Value::meta(Meta::Span(tok.span))),
        ("Token", "name", Some(Meta::Token(tok))) => {
            Ok(Value::option(match tok.lexed.as_slice() {
                [l] if matches!(l.kind, SyntaxKind::LOWER_IDENT | SyntaxKind::UPPER_IDENT) => {
                    Some(Value::meta(Meta::Name(NameValue {
                        text: Arc::from(&*l.text),
                        origin: l.origin.clone(),
                        span: tok.span,
                    })))
                }
                _ => None,
            }))
        }
        ("Text", "value", Some(Meta::Text(text))) => Ok(Value::str(&*text.value)),
        ("Text", "span", Some(Meta::Text(text))) => {
            let (start, end) = (values[1].as_int(), values[2].as_int());
            let len = text.value.len();
            match (usize::try_from(start), usize::try_from(end)) {
                (Ok(a), Ok(b)) if a <= b && b <= len => {
                    Ok(Value::meta(Meta::Span(text_span(&mach.io, &text, a, b))))
                }
                _ => panic(
                    "bounds",
                    format!(
                        "the bytes from {start} to {end} are out of bounds for a text of {len} bytes"
                    ),
                ),
            }
        }
        ("Text", "lex", Some(Meta::Text(text))) => match super::tokens::lex(&mach.io, &text) {
            Ok((items, close)) => Ok(super::tokens::record(&items, close)),
            Err(err) => Err(Flow::Raise(Value::meta(Meta::Error(err)))),
        },
        ("Name", "text", Some(Meta::Name(n))) => Ok(Value::str(&*n.text)),
        ("Name", "span", Some(Meta::Name(n))) => Ok(Value::meta(Meta::Span(n.span))),
        ("Expr" | "Pattern" | "Type" | "FieldInit", "span", Some(Meta::Code(code))) => {
            Ok(Value::meta(Meta::Span(code.span)))
        }
        ("Error", "note", Some(Meta::Error(mut err))) => {
            if let (Some(Meta::Span(at)), Some(text)) = (meta(1), values.get(2))
                && err.notes.len() < 3
            {
                err.notes.push((at, text.as_str().to_owned()));
            }
            Ok(Value::meta(Meta::Error(err)))
        }
        _ => unreachable!("the table names every native of `meta.{owner}`: {name}"),
    }
}

/// The function `name` of `std.meta`.
pub(crate) fn function<'a>(m: &mut Machine<'a>, name: &str, values: &mut [Value<'a>]) -> R<'a> {
    match name {
        "fresh" => {
            let id = m.io.fresh;
            m.io.fresh += 1;
            Ok(Value::meta(Meta::Name(NameValue {
                text: Arc::from(values.first().map_or("", Value::as_str)),
                origin: Origin::Fresh(id),
                span: m.io.use_span(),
            })))
        }
        "error" => {
            let at = match values.first().and_then(Value::as_meta) {
                Some(Meta::Span(s)) => *s,
                _ => m.io.use_span(),
            };
            let message = values.get(1).map_or("", Value::as_str).to_owned();
            Ok(Value::meta(Meta::Error(ErrorValue {
                at,
                message,
                notes: Vec::new(),
            })))
        }
        "parse_expr" => super::parse::parsed(m, CodeForm::Expr, values),
        "parse_pattern" => super::parse::parsed(m, CodeForm::Pattern, values),
        "parse_type" => super::parse::parsed(m, CodeForm::Type, values),
        _ => unreachable!("the table names every function of `std.meta`: {name}"),
    }
}
