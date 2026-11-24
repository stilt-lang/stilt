//! The spaces between the tokens of a macro's declaration, which no tree of expressions holds:
//! each is decided by the token before it and its own kind, as the spaces of code are where the
//! tokens are the same (macros.formatting).

use stilt_syntax::SyntaxKind::{self, *};
use stilt_syntax::SyntaxToken;

use crate::trivia::is_trivia;

/// What the last token written does, for the space after it.
#[derive(Clone, Copy, Debug)]
pub(super) struct Prev {
    pub(super) kind: SyntaxKind,
    /// The last character of its text.
    pub(super) last: char,
    /// Whether it ends an operand, so that a `(` or a `[` after it applies to it.
    pub(super) operand: bool,
    /// Whether no space goes after it.
    pub(super) tight_after: bool,
}

/// How a token stands among its neighbours.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Shape {
    /// Whether no space goes before it.
    pub(super) tight_before: bool,
    /// Whether no space goes after it.
    pub(super) tight_after: bool,
    /// Whether it ends an operand.
    pub(super) operand: bool,
}

impl Shape {
    /// A token with no space before it, which ends an operand: a `)` or a repetition's `*`.
    pub(super) const CLOSE: Self = Self {
        tight_before: true,
        tight_after: false,
        operand: true,
    };
    /// A token with no space before it and one after: a `,`, a `:` or a `;`.
    pub(super) const PUNCT: Self = Self {
        tight_before: true,
        tight_after: false,
        operand: false,
    };
    /// A token with no space after it: a prefix operator, a `$` or an opening bracket.
    const PREFIX: Self = Self {
        tight_before: false,
        tight_after: true,
        operand: false,
    };
}

/// The brackets of the sequence being written that change the spaces inside them: the `<` of
/// type arguments still open, and whether a closure's `|` opened its parameters.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Open {
    angles: usize,
    bar: bool,
}

/// How a token stands, after `prev`, among the open brackets of its sequence, which it updates.
pub(super) fn shape(token: &SyntaxToken, prev: Option<Prev>, open: &mut Open) -> Shape {
    let after_operand = prev.is_some_and(|p| p.operand);
    let after = |kind: SyntaxKind| prev.is_some_and(|p| p.kind == kind);
    let in_rep = token.parent().is_some_and(|p| p.kind() == MACRO_REP);
    match token.kind() {
        BANG if after(LOWER_IDENT) => Shape {
            tight_before: true,
            ..Shape::PREFIX
        },
        DOLLAR | AT | STRING_HEAD | BANG => Shape::PREFIX,
        L_PAREN | L_BRACK => Shape {
            tight_before: after_operand || after(FN_KW) || after(BANG),
            ..Shape::PREFIX
        },
        R_PAREN | R_BRACK | QUESTION | STRING_TAIL => Shape::CLOSE,
        STAR | PLUS if in_rep => Shape::CLOSE,
        R_CURLY => Shape {
            tight_before: after(L_CURLY),
            ..Shape::CLOSE
        },
        COMMA | COLON | SEMICOLON | FORMAT => Shape::PUNCT,
        STRING_MID => Shape {
            tight_before: true,
            ..Shape::PREFIX
        },
        DOT => Shape {
            tight_before: !after(INT),
            ..Shape::PREFIX
        },
        DOT2 | DOT2EQ => Shape {
            tight_before: after_operand,
            ..Shape::PREFIX
        },
        MINUS if !after_operand => Shape {
            tight_after: !apart_from_number(token),
            ..Shape::PREFIX
        },
        L_ANGLE | R_ANGLE | SHR | PIPE => bracket(token.kind(), prev, open),
        kind => Shape {
            operand: is_operand(kind),
            ..Shape::default()
        },
    }
}

/// How a `<`, a `>`, a `>>` or a `|` stands: as the bracket of type arguments or of a
/// closure's parameters, which it opens or closes, or as an operator.
fn bracket(kind: SyntaxKind, prev: Option<Prev>, open: &mut Open) -> Shape {
    let after_operand = prev.is_some_and(|p| p.operand);
    match kind {
        L_ANGLE if prev.is_some_and(|p| p.kind == UPPER_IDENT) => {
            open.angles += 1;
            Shape {
                tight_before: true,
                ..Shape::PREFIX
            }
        }
        R_ANGLE | SHR if open.angles > 0 => {
            let closes = if kind == SHR { 2 } else { 1 };
            open.angles = open.angles.saturating_sub(closes);
            Shape::CLOSE
        }
        PIPE if open.bar => {
            open.bar = false;
            Shape::PUNCT
        }
        PIPE if !after_operand => {
            open.bar = true;
            Shape::PREFIX
        }
        _ => Shape::default(),
    }
}

/// Whether one space goes between the token `prev` and one of `shape` whose text is `text`.
/// Two tokens are never written against each other where their text would read as other
/// tokens, as `- >` would as `->`, or as braces would as an escaped one in a string.
pub(super) fn spaced(prev: Prev, shape: Shape, kind: SyntaxKind, text: &str) -> bool {
    let first = text.chars().next().unwrap_or(' ');
    if matches!((prev.last, first), ('{', '{') | ('}', '}')) {
        return true;
    }
    if kind == R_CURLY {
        return prev.kind != L_CURLY;
    }
    !(prev.tight_after || shape.tight_before) || (is_operator(prev.last) && is_operator(first))
}

/// Whether a character may end or start an operator, which another one could join.
fn is_operator(c: char) -> bool {
    "+-*/%=<>!&|^.:?@~#".contains(c)
}

/// The tokens that end an operand.
fn is_operand(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        LOWER_IDENT
            | UPPER_IDENT
            | INT
            | FLOAT
            | STRING
            | TRUE_KW
            | FALSE_KW
            | SELF_KW
            | SELF_TYPE_KW
    )
}

/// Whether a `-` is followed by a number, with spaces or a line break between them, which makes it
/// a negation rather than part of the literal (numbers.negative-literals), so that it keeps its
/// space.
fn apart_from_number(minus: &SyntaxToken) -> bool {
    let mut next = minus.next_token();
    let mut apart = false;
    while let Some(token) = next.as_ref().filter(|t| is_trivia(t.kind())) {
        apart = true;
        next = token.next_token();
    }
    apart && next.is_some_and(|t| matches!(t.kind(), INT | FLOAT))
}

/// Whether a newline after a token of kind `kind` can end a statement
/// (lexical.terminator-insertion), as the separators of a declaration need.
pub(super) fn ends_statement(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        LOWER_IDENT
            | UPPER_IDENT
            | INT
            | FLOAT
            | STRING
            | STRING_TAIL
            | TRUE_KW
            | FALSE_KW
            | SELF_KW
            | SELF_TYPE_KW
            | RETURN_KW
            | BREAK_KW
            | CONTINUE_KW
            | UNSAFE_KW
            | R_PAREN
            | R_BRACK
            | R_CURLY
            | QUESTION
            | R_ANGLE
            | SHR
    )
}

/// Whether a token of kind `kind` continues the line before it (lexical.continuation-lines), so
/// that no newline before it ends a statement.
pub(super) fn continues_line(kind: SyntaxKind) -> bool {
    matches!(kind, DOT | ELSE_KW | CATCH_KW | PIPE)
}
