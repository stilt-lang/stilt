//! Tokens as a macro reads them (macros.tokens-and-code): the tokens of lexical.tokens, as written,
//! each group one token holding its own, each interpolated string one token, without the separators
//! that newlines insert, and without doc comments; each keeps its tokens as code, the separators
//! inside its groups included, which the parsers read (macros.part-forms).

use std::sync::Arc;

use stilt_hir::hir::Name;
use stilt_hir::procs::Origin;
use stilt_syntax::SyntaxKind::{
    self, FLOAT, INT, L_BRACK, L_CURLY, L_PAREN, LOWER_IDENT, R_BRACK, R_CURLY, R_PAREN, SEP,
    STRING, STRING_HEAD, STRING_TAIL, UPPER_IDENT,
};
use stilt_syntax::text::literal_value;

use crate::run::Io;
use crate::value::{
    ErrorValue, Lex, Meta, Span, Text, TextOrigin, Token, TokenKind, Value, meta_item,
};

/// A token before it is read into a tree: as code, its span, and whether a newline inserted
/// it.
#[derive(Clone, Debug)]
pub(crate) struct Raw {
    pub(crate) lex: Lex,
    pub(crate) span: Span,
    pub(crate) inserted: bool,
    /// For a string literal, its text.
    pub(crate) text: Option<Text>,
}

fn opens(kind: SyntaxKind) -> bool {
    matches!(kind, L_PAREN | L_BRACK | L_CURLY | STRING_HEAD)
}

fn closes(kind: SyntaxKind) -> bool {
    matches!(kind, R_PAREN | R_BRACK | R_CURLY | STRING_TAIL)
}

/// The index of the token that closes the one at `i`.
fn closing(raws: &[Raw], i: usize) -> usize {
    let mut depth = 0usize;
    for (j, r) in raws.iter().enumerate().skip(i) {
        if opens(r.lex.kind) {
            depth += 1;
        } else if closes(r.lex.kind) {
            depth = depth.saturating_sub(1);
            if depth == 0 {
                return j;
            }
        }
    }
    raws.len().saturating_sub(1)
}

/// The tokens of `raws`, groups and interpolated strings gathered.
pub(crate) fn tree(raws: &[Raw]) -> Vec<Token> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < raws.len() {
        let r = &raws[i];
        if r.inserted {
            i += 1;
            continue;
        }
        if opens(r.lex.kind) {
            let j = closing(raws, i);
            let lexed: Vec<Lex> = raws[i..=j].iter().map(|x| x.lex.clone()).collect();
            let close = raws[j].span;
            let span = r.span.to(close);
            let kind = if r.lex.kind == STRING_HEAD {
                TokenKind::Interpolated
            } else {
                TokenKind::Group(r.lex.kind, Arc::new(tree(&raws[i + 1..j])), close)
            };
            out.push(Token {
                lexed: Arc::new(lexed),
                span,
                kind,
            });
            i = j + 1;
            continue;
        }
        out.push(Token {
            lexed: Arc::new(vec![r.lex.clone()]),
            span: r.span,
            kind: kind_of(r),
        });
        i += 1;
    }
    out
}

/// What a single token is.
fn kind_of(r: &Raw) -> TokenKind {
    let text: Arc<str> = Arc::from(&*r.lex.text);
    match r.lex.kind {
        LOWER_IDENT | UPPER_IDENT => TokenKind::Word(text),
        INT | FLOAT => TokenKind::Number(text),
        STRING => TokenKind::Text(r.text.clone().unwrap_or_else(|| Text {
            value: Arc::from(literal_value(&text).as_str()),
            origin: TextOrigin::Literal {
                raw: text.clone(),
                at: r.span,
            },
        })),
        SEP => TokenKind::Punct(Arc::from(";")),
        _ if text.starts_with(|c: char| c.is_ascii_lowercase() || c == '_') => {
            TokenKind::Word(text)
        }
        _ => TokenKind::Punct(text),
    }
}

/// The use's tokens of the indices `indices`.
pub(crate) fn given(io: &Io<'_>, indices: &[u32]) -> Vec<Raw> {
    indices
        .iter()
        .filter_map(|&i| {
            let l = io.call.lexemes.get(i as usize)?;
            let inserted = l.kind == SEP && l.text.is_empty();
            let text = if l.kind == SEP {
                Name::from(";")
            } else {
                l.text
            };
            Some(Raw {
                lex: Lex {
                    kind: l.kind,
                    text,
                    origin: Origin::Given(i),
                },
                span: Span {
                    start: l.at.start,
                    end: l.at.end,
                    file: None,
                },
                inserted,
                text: None,
            })
        })
        .collect()
}

/// A `Tokens` record of `items`, ended at `close`.
pub(crate) fn record<'a>(items: &[Token], close: Span) -> Value<'a> {
    let items = items
        .iter()
        .map(|t| Value::meta(Meta::Token(t.clone())))
        .collect();
    Value::record(
        meta_item("Tokens"),
        vec![
            (Name::from("items"), Value::list(items)),
            (Name::from("close"), Value::meta(Meta::Span(close))),
        ],
    )
}

/// The tokens and the closing span of a `Tokens` record.
pub(crate) fn of_record(v: &Value<'_>) -> (Vec<Token>, Span) {
    let items = v
        .field("items")
        .map(|xs| {
            xs.as_list()
                .iter()
                .filter_map(|t| match t.as_meta() {
                    Some(Meta::Token(t)) => Some(t.clone()),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default();
    let close = match v.field("close").and_then(Value::as_meta) {
        Some(Meta::Span(s)) => *s,
        _ => Span {
            start: 0,
            end: 0,
            file: None,
        },
    };
    (items, close)
}

/// A token's kind as `std.meta`'s `Kind`.
pub(crate) fn kind_value<'a>(k: &TokenKind) -> Value<'a> {
    let v = |name: &str, payload| Value::variant(meta_item(name), payload);
    match k {
        TokenKind::Word(s) => v("Word", vec![Value::str(&**s)]),
        TokenKind::Number(s) => v("Number", vec![Value::str(&**s)]),
        TokenKind::Text(t) => v("Text", vec![Value::meta(Meta::Text(t.clone()))]),
        TokenKind::Interpolated => v("Interpolated", Vec::new()),
        TokenKind::Punct(s) => v("Punct", vec![Value::str(&**s)]),
        TokenKind::Group(open, items, close) => {
            let delim = match open {
                L_PAREN => "Paren",
                L_BRACK => "Bracket",
                _ => "Brace",
            };
            v("Group", vec![v(delim, Vec::new()), record(items, *close)])
        }
    }
}

/// macros.tokens-and-code's `Text.lex`: the text's tokens as lexical.tokens lexes them, or the
/// error at the first character it can't lex.
pub(crate) fn lex(io: &Io<'_>, x: &Text) -> Result<(Vec<Token>, Span), ErrorValue> {
    let place = |a: usize, b: usize| crate::meta::natives::text_span(io, x, a, b);
    let tokens = stilt_syntax::forms::lex_text(&x.value).map_err(|(at, message)| {
        let at = usize::from(at);
        ErrorValue {
            at: place(at, at + 1),
            message,
            notes: Vec::new(),
        }
    })?;
    let raws: Vec<Raw> = tokens
        .iter()
        .map(|t| {
            let (a, b) = (usize::from(t.range.start()), usize::from(t.range.end()));
            let span = place(a, b);
            let written = &x.value[a..b];
            let text = if t.kind == SEP { ";" } else { written };
            let string = (t.kind == STRING).then(|| Text {
                value: Arc::from(literal_value(written).as_str()),
                origin: TextOrigin::Literal {
                    raw: Arc::from(written),
                    at: span,
                },
            });
            Raw {
                lex: Lex {
                    kind: t.kind,
                    text: Name::from(text),
                    origin: crate::meta::natives::placed(io, span),
                },
                span,
                inserted: t.inserted,
                text: string,
            }
        })
        .collect();
    let close = raws.last().map_or_else(|| place(0, 0), |r| r.span);
    Ok((tree(&raws), close))
}
