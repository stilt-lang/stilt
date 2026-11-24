//! The diagnostics of syntax errors: what was found and what was expected, in words, and for
//! another language's syntax, the Stilt form (reference/messages.md).

use stilt_diag::{Diagnostic, codes};

use crate::SyntaxKind::{self, *};
use crate::fixes;
use crate::foreign::{self, Cx};
use crate::lexer::{LexError, Lexed, lexicon};
use crate::parser::{Expected, ParseError};
use crate::stream::Sig;

/// The diagnostic of a lexical error, with the fix of a `{{`.
pub(crate) fn lexical_error(text: &str, error: &LexError) -> Diagnostic {
    let start = usize::from(error.range.start());
    if let Some(found) = crate::foreign_marks::lexical(text, error.code, start) {
        let d = Diagnostic::new(error.code, error.range, found.message).with_help(found.help);
        return match found.fix {
            Some(fix) => d.with_fix(fix),
            None => d,
        };
    }
    let d = Diagnostic::new(error.code, error.range, error.message.clone());
    if error.code == codes::E0006 && text[start..].starts_with("{{") {
        d.with_fix(fixes::doubled_braces(text, start))
    } else {
        d
    }
}

/// The diagnostic of a syntax error found at a token. A doc comment that nothing documents is
/// the error, rather than the token after it.
pub(crate) fn grammar_error(
    text: &str,
    lexed: &Lexed,
    tokens: &[Sig],
    error: ParseError,
) -> Diagnostic {
    let index = if error.token > 0 && tokens[error.token - 1].kind == DOC {
        error.token - 1
    } else {
        error.token
    };
    let token = tokens[index];
    let cx = Cx {
        text,
        tokens,
        at: index,
    };
    if let Some(found) = foreign::explain(&cx) {
        let d = Diagnostic::new(codes::E0100, token.range, found.message).with_help(found.help);
        return match found.fix {
            Some(fix) => d.with_fix(fix),
            None => d,
        };
    }
    let found = found(text, lexed, token);
    if let Some(fix) = fixes::braced_assignment(tokens, index) {
        let message = format!(
            "unexpected {found}: the body of an arm is an expression, and an assignment is a \
             statement"
        );
        return Diagnostic::new(codes::E0100, token.range, message).with_fix(fix);
    }
    let message = match (token.kind, error.expected.and_then(expected)) {
        (DOC | MISPLACED_DOC, _) => found,
        (_, Some(expected)) => format!("expected {expected}, found {found}"),
        (_, None) => format!("unexpected {found}"),
    };
    Diagnostic::new(codes::E0100, token.range, message)
}

/// What the token at which a part breaks is, in words.
fn found(text: &str, lexed: &Lexed, token: Sig) -> String {
    let spelled = || {
        let raw = lexed.tokens[token.start as usize];
        &text[raw.start as usize..(raw.start + raw.len) as usize]
    };
    match token.kind {
        DOC | MISPLACED_DOC => "a doc comment must come directly before a declaration".to_owned(),
        SEP => "the end of the statement".to_owned(),
        EOF => "the end of the file".to_owned(),
        INT | FLOAT => format!("the number `{}`", spelled().replace('_', "")),
        STRING | STRING_HEAD => "a string".to_owned(),
        STRING_MID | STRING_TAIL | FORMAT => "the rest of a string".to_owned(),
        _ => format!("`{}`", spelled()),
    }
}

/// What the grammar expected, in words: a form, or a token as it is spelled.
fn expected(what: Expected) -> Option<String> {
    match what {
        Expected::Form(form) => Some(form.to_owned()),
        Expected::Token(kind) => spelling(kind).map(|s| format!("`{s}`")),
        Expected::CommaOr(close) => spelling(close).map(|s| format!("`,` or `{s}`")),
    }
}

/// How a token of `kind` is spelled, if every token of the kind is spelled alike.
fn spelling(kind: SyntaxKind) -> Option<&'static str> {
    let words = lexicon::KEYWORDS.iter().chain(&lexicon::CONTEXTUAL);
    (words.chain(&lexicon::PUNCTUATION))
        .find(|(_, k)| *k == kind)
        .map(|(spelled, _)| *spelled)
}
