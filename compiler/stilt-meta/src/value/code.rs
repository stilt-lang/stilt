//! The values of `std.meta` that only a macro's run makes (macros.tokens-and-code): spans, tokens,
//! texts, names, code and errors.

use std::sync::Arc;

use stilt_hir::hir::{CodeForm, Name};
use stilt_hir::procs::Origin;
use stilt_syntax::SyntaxKind;

/// A place in the use's file, relative to the use, or in the file of this index among those
/// the use names (macros.tokens-and-code).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Span {
    pub(crate) start: i64,
    pub(crate) end: i64,
    pub(crate) file: Option<u32>,
}

impl Span {
    pub(crate) fn to(self, other: Span) -> Span {
        if self.file == other.file {
            Span {
                end: other.end.max(self.start),
                ..self
            }
        } else {
            self
        }
    }
}

/// A token as code: its kind as the parser reads it, its text, and where it came from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Lex {
    pub(crate) kind: SyntaxKind,
    pub(crate) text: Name,
    pub(crate) origin: Origin,
}

/// Where a text's value is written.
#[derive(Clone, Debug)]
pub(crate) enum TextOrigin {
    /// A string literal of the use's file, as written, quotes included, at this span.
    Literal { raw: Arc<str>, at: Span },
    /// The text of the file of this index among those the use names.
    File(u32),
}

#[derive(Clone, Debug)]
pub(crate) struct Text {
    pub(crate) value: Arc<str>,
    pub(crate) origin: TextOrigin,
}

/// What a token is (macros.tokens-and-code's `Kind`).
#[derive(Clone, Debug)]
pub(crate) enum TokenKind {
    Word(Arc<str>),
    Number(Arc<str>),
    Text(Text),
    Interpolated,
    Punct(Arc<str>),
    /// Its brackets' kind (`(`, `[` or `{`), its tokens, and its closing bracket's span.
    Group(SyntaxKind, Arc<Vec<Token>>, Span),
}

/// A token: its tokens as code, all of a group's or an interpolated string's, its span and
/// what it is.
#[derive(Clone, Debug)]
pub(crate) struct Token {
    pub(crate) lexed: Arc<Vec<Lex>>,
    pub(crate) span: Span,
    pub(crate) kind: TokenKind,
}

/// An identifier: as written, where it came from, and its span.
#[derive(Clone, Debug)]
pub(crate) struct NameValue {
    pub(crate) text: Arc<str>,
    pub(crate) origin: Origin,
    pub(crate) span: Span,
}

/// Code, its tokens as the expansion holds them.
#[derive(Clone, Debug)]
pub(crate) struct Code {
    pub(crate) tokens: Arc<super::Counted<Vec<Lex>>>,
    pub(crate) span: Span,
    pub(crate) form: CodeForm,
}

/// A diagnostic a macro raises.
#[derive(Clone, Debug)]
pub(crate) struct ErrorValue {
    pub(crate) at: Span,
    pub(crate) message: String,
    pub(crate) notes: Vec<(Span, String)>,
}

/// The native values of `std.meta`.
#[derive(Clone, Debug)]
pub(crate) enum Meta {
    Span(Span),
    Token(Token),
    Text(Text),
    Name(NameValue),
    Code(Code),
    Error(ErrorValue),
}
