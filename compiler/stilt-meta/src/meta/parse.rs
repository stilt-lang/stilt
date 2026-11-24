//! The parsers that a cursor calls (macros.cursor): the longest run of tokens that is a whole
//! expression, pattern or type of the language's own grammar, read with no terminator at its
//! top level (macros.part-forms), that stops before a `,`, a `;` or the end.

use std::sync::Arc;

use stilt_hir::hir::CodeForm;
use stilt_syntax::SyntaxKind;
use stilt_syntax::forms::{Form, Piece, parse_form};

use super::tokens::of_record;
use crate::eval::{Flow, Machine, R};
use crate::value::{Code, ErrorValue, Lex, Meta, Span, Token, TokenKind, Value};

fn form_of(form: CodeForm) -> Form {
    match form {
        CodeForm::Expr | CodeForm::Field => Form::Expr,
        CodeForm::Pattern => Form::Pattern,
        CodeForm::Type => Form::Type,
    }
}

fn form_name(form: CodeForm) -> &'static str {
    match form {
        CodeForm::Expr | CodeForm::Field => "an expression",
        CodeForm::Pattern => "a pattern",
        CodeForm::Type => "a type",
    }
}

/// A token as a message shows it.
fn shown(t: &Token) -> String {
    match &t.kind {
        TokenKind::Word(x) | TokenKind::Number(x) | TokenKind::Punct(x) => format!("`{x}`"),
        TokenKind::Text(_) => "a string".to_owned(),
        TokenKind::Interpolated => "an interpolated string".to_owned(),
        TokenKind::Group(SyntaxKind::L_PAREN, ..) => "`(`".to_owned(),
        TokenKind::Group(SyntaxKind::L_BRACK, ..) => "`[`".to_owned(),
        TokenKind::Group(..) => "`{`".to_owned(),
    }
}

/// The tokens of a run of tokens as code.
fn code(run: &[Token]) -> Vec<Lex> {
    run.iter().flat_map(|t| t.lexed.iter().cloned()).collect()
}

/// Where the parse of `lexes` as `form` fails, by index, or `None` when it parses whole.
fn parse_error(form: CodeForm, lexes: &[Lex]) -> Option<usize> {
    let pieces: Vec<Piece<'_>> = lexes
        .iter()
        .map(|l| Piece {
            kind: l.kind,
            text: &l.text,
        })
        .collect();
    let parsed = parse_form(&pieces, form_of(form));
    if parsed.is_whole(pieces.len()) {
        None
    } else {
        Some(parsed.error.unwrap_or(parsed.taken))
    }
}

/// Whether the run of `k` tokens from `at` stops before a `,`, a `;` or the end.
fn stops(items: &[Token], at: usize, k: usize) -> bool {
    match items.get(at + k) {
        None => true,
        Some(t) => matches!(&t.kind, TokenKind::Punct(p) if &**p == "," || &**p == ";"),
    }
}

/// `parse_expr(ts, at)` and the others: the code read, and where the next token is.
pub(super) fn parsed<'a>(_m: &mut Machine<'a>, form: CodeForm, values: &[Value<'a>]) -> R<'a> {
    let (items, close) = of_record(&values[0]);
    let at = values.get(1).map_or(0, Value::as_int);
    match parse(form, &items, at, close) {
        Ok((code, next)) => Ok(Value::tuple(vec![
            Value::meta(Meta::Code(code)),
            Value::i64(next as i128),
        ])),
        Err(e) => Err(Flow::Raise(Value::meta(Meta::Error(e)))),
    }
}

fn parse(
    form: CodeForm,
    items: &[Token],
    at: i128,
    close: Span,
) -> Result<(Code, usize), ErrorValue> {
    let n = items.len();
    let Some(at) = usize::try_from(at).ok().filter(|&a| a <= n) else {
        let at = usize::try_from(at.max(0)).unwrap_or(0).min(n);
        return Err(failure(form, items, at, close));
    };
    for k in (1..=n - at).rev() {
        if stops(items, at, k) && parse_error(form, &code(&items[at..at + k])).is_none() {
            let run = &items[at..at + k];
            let code = Code {
                tokens: Arc::new(crate::value::Counted::new(code(run))),
                span: run[0].span.to(run[k - 1].span),
                form,
            };
            return Ok((code, at + k));
        }
    }
    if at == n {
        return Err(ErrorValue {
            at: close,
            message: format!("expected {}, found the end", form_name(form)),
            notes: Vec::new(),
        });
    }
    Err(failure(form, items, at, close))
}

/// Where a run that parses as no form fails: the token where the parser stops, or what ends
/// the run.
fn failure(form: CodeForm, items: &[Token], at: usize, close: Span) -> ErrorValue {
    let n = items.len();
    let s = (1..=n.saturating_sub(at))
        .find(|&k| stops(items, at, k))
        .unwrap_or(0);
    let ending = items.get(at + s);
    let run = &items[at.min(n)..(at + s).min(n)];
    let found = parse_error(form, &code(run)).and_then(|e| {
        let mut seen = 0;
        run.iter().find(|t| {
            seen += t.lexed.len();
            e < seen
        })
    });
    let message = |what: String| format!("expected {}, found {what}", form_name(form));
    match found.or(ending) {
        Some(t) => ErrorValue {
            at: t.span,
            message: message(shown(t)),
            notes: Vec::new(),
        },
        None => ErrorValue {
            at: close,
            message: message("the end".to_owned()),
            notes: Vec::new(),
        },
    }
}
