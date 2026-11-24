//! The spaces within a line: whether one space or none goes between two tokens, by what each
//! token does where it stands.

use stilt_syntax::SyntaxKind::{self, *};
use stilt_syntax::SyntaxToken;

/// What a token does, as far as the spaces around it go.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Class {
    /// A name, a literal or another atom.
    Word,
    /// An integer literal, after which the `.` of a numbered field keeps its space, since `1 .0`
    /// reads a field where `1.0` reads a float (lexical.digits-after-dot).
    Number,
    /// A keyword, a binary operator, or another token with a space on each side.
    Spaced,
    /// A `(` or a `[` that groups or starts a list.
    Open,
    /// The `(` of a call, a list of parameters or a payload, or the `[` of an index, which
    /// follow what they apply to without a space.
    Tight,
    /// A `)` or a `]`.
    Close,
    /// The `{` of a block, a body or a record, with a space on each side.
    Brace,
    /// The `}` that closes a brace.
    BraceClose,
    /// The `{` of a row, as in `/ {io, raise<str>}`, which has no space inside.
    RowOpen,
    /// The `}` of a row.
    RowClose,
    Comma,
    Colon,
    /// The `.` of a field or a path.
    Dot,
    /// The `.` of a numbered field, as in `t.0`.
    DotNumber,
    /// The `.` that starts a key path.
    KeyDot,
    /// A prefix `-` or `!`.
    Prefix,
    /// A prefix `-` that the source separates from the number after it, which makes it a negation
    /// rather than part of the literal (numbers.negative-literals). The space is part of what the
    /// program means, and the tree doesn't show it.
    SpacedPrefix,
    /// The `..` or `..=` of a range, which has no space on either side.
    Range,
    /// The `..` of a rest pattern that binds a name, written against it.
    Rest,
    /// The `<` of generics or type arguments.
    AngleOpen,
    /// The `>` of generics or type arguments.
    AngleClose,
    /// The `|` that opens a closure's parameters.
    BarOpen,
    /// The `|` that closes a closure's parameters.
    BarClose,
    /// The start of an interpolated string, up to its first `{`.
    StrOpen,
    /// The text between two interpolations.
    StrMid,
    /// The end of an interpolated string, from its last `}`.
    StrClose,
    /// The format spec of an interpolation.
    Format,
}

/// The class of a token of the tree.
pub(crate) fn class(token: &SyntaxToken) -> Class {
    let parent = token.parent().map(|p| p.kind());
    let is = |kind: SyntaxKind| parent == Some(kind);
    match token.kind() {
        L_PAREN
            if matches!(
                parent,
                Some(
                    ARG_LIST
                        | PARAM_LIST
                        | PAYLOAD_LIST
                        | VARIANT_PAT
                        | PARAM_TYPE_LIST
                        | RESUME_EXPR
                )
            ) =>
        {
            Class::Tight
        }
        L_BRACK if is(INDEX_EXPR) => Class::Tight,
        L_PAREN | L_BRACK => Class::Open,
        R_PAREN | R_BRACK => Class::Close,
        L_CURLY if is(ROW) => Class::RowOpen,
        R_CURLY if is(ROW) => Class::RowClose,
        L_CURLY => Class::Brace,
        R_CURLY => Class::BraceClose,
        COMMA => Class::Comma,
        COLON => Class::Colon,
        DOT if is(KEY_PATH_EXPR) => Class::KeyDot,
        DOT if names_number(token) => Class::DotNumber,
        DOT => Class::Dot,
        MINUS if (is(PREFIX_EXPR) || is(LITERAL_PAT)) && apart_from_number(token) => {
            Class::SpacedPrefix
        }
        MINUS | BANG if is(PREFIX_EXPR) || is(LITERAL_PAT) => Class::Prefix,
        // A splice's `$` and the `..` of a spread one are written against what they splice
        // (macros.splices).
        DOLLAR if is_splice(parent) => Class::Prefix,
        DOT2 if is(SPLICE_SPREAD) => Class::Rest,
        // A value argument's `-` is part of its literal (generics.value-arguments).
        MINUS if is(VALUE_ARG) => Class::Prefix,
        DOT2 if is(REST_PAT) => rest(token),
        // A spread, a pack among generics, and an update's base are written against what they
        // spread (records.update; variadics.packs, variadics.type-spreads and
        // variadics.spread-expressions); an open record type's `..` stands alone
        // (records.open-parameter-types).
        DOT2 if is(SPREAD_EXPR) || is(SPREAD_TYPE) || is(TYPE_PARAM) => Class::Rest,
        DOT2 if is(RECORD_TYPE) => Class::Word,
        DOT2 | DOT2EQ => Class::Range,
        L_ANGLE if !is(BINARY_EXPR) => Class::AngleOpen,
        R_ANGLE if !is(BINARY_EXPR) => Class::AngleClose,
        PIPE if is(CLOSURE_EXPR) => closure_bar(token),
        STRING_HEAD => Class::StrOpen,
        STRING_MID => Class::StrMid,
        STRING_TAIL => Class::StrClose,
        FORMAT => Class::Format,
        INT if is(LITERAL) => Class::Number,
        kind if is_spaced(kind) => Class::Spaced,
        _ => Class::Word,
    }
}

/// Whether a node is a splice (macros.splices).
fn is_splice(kind: Option<SyntaxKind>) -> bool {
    matches!(
        kind,
        Some(SPLICE_EXPR | SPLICE_PAT | SPLICE_TYPE | SPLICE_NAME | SPLICE_SPREAD)
    )
}

/// The `..` of a rest pattern is written against the name it binds, and stands alone as a word
/// when it binds none.
fn rest(token: &SyntaxToken) -> Class {
    if token.next_sibling_or_token().is_some() {
        Class::Rest
    } else {
        Class::Word
    }
}

/// Whether a `-` is followed by a number literal, with spaces or a line break between them.
fn apart_from_number(minus: &SyntaxToken) -> bool {
    let mut next = minus.next_sibling_or_token();
    let mut apart = false;
    while let Some(e) = &next {
        if !crate::trivia::is_trivia(e.kind()) {
            break;
        }
        apart = true;
        next = e.next_sibling_or_token();
    }
    apart
        && next.is_some_and(|e| match e {
            rowan::NodeOrToken::Token(t) => matches!(t.kind(), INT | FLOAT),
            rowan::NodeOrToken::Node(n) => n
                .first_token()
                .is_some_and(|t| matches!(t.kind(), INT | FLOAT)),
        })
}

/// Whether a `.` names a numbered field.
fn names_number(dot: &SyntaxToken) -> bool {
    dot.siblings_with_tokens(rowan::Direction::Next)
        .skip(1)
        .find(|e| !crate::trivia::is_trivia(e.kind()))
        .is_some_and(|e| e.kind() == INT)
}

/// The first `|` of a closure opens its parameters, and the second closes them.
fn closure_bar(token: &SyntaxToken) -> Class {
    let opens = token
        .siblings_with_tokens(rowan::Direction::Prev)
        .skip(1)
        .all(|e| e.kind() != PIPE);
    if opens {
        Class::BarOpen
    } else {
        Class::BarClose
    }
}

/// The tokens with a space on each side: the operators other than prefixes, ranges and
/// access, and the keywords that aren't atoms.
fn is_spaced(kind: SyntaxKind) -> bool {
    is_operator(kind) || is_keyword(kind)
}

fn is_operator(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        PLUS | MINUS
            | STAR
            | SLASH
            | PERCENT
            | PLUS_PERCENT
            | MINUS_PERCENT
            | STAR_PERCENT
            | EQ2
            | NEQ
            | L_ANGLE
            | LTEQ
            | R_ANGLE
            | GTEQ
            | AMP2
            | PIPE2
            | AMP
            | PIPE
            | CARET
            | SHL
            | SHR
            | EQ
            | PLUS_EQ
            | MINUS_EQ
            | STAR_EQ
            | SLASH_EQ
            | PERCENT_EQ
            | PLUS_PERCENT_EQ
            | MINUS_PERCENT_EQ
            | STAR_PERCENT_EQ
            | AMP_EQ
            | PIPE_EQ
            | CARET_EQ
            | SHL_EQ
            | SHR_EQ
            | THIN_ARROW
            | FAT_ARROW
    )
}

/// The keywords that aren't atoms, such as `self` or `break`, and the contextual keywords
/// that start a clause (lexical.keywords and lexical.contextual-keywords).
fn is_keyword(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        ASSERT_KW
            | YIELD_KW
            | CATCH_KW
            | CONST_KW
            | ELSE_KW
            | FN_KW
            | FOR_KW
            | IF_KW
            | IMPL_KW
            | IN_KW
            | INOUT_KW
            | LET_KW
            | LOOP_KW
            | MATCH_KW
            | MODULE_KW
            | PUB_KW
            | RAISE_KW
            | RETURN_KW
            | TEST_KW
            | TRAIT_KW
            | TRY_KW
            | TYPE_KW
            | USE_KW
            | VAR_KW
            | WHILE_KW
            | WITHOUT_KW
            | BECAUSE_KW
            | ESCAPING_KW
            | EFFECT_KW
            | HANDLER_KW
            | WITH_KW
            | WHEN_KW
            | UNSAFE_KW
    )
}

/// Whether one space goes between a token of class `a` and the token of class `b` after it.
/// A side that wants no space wins over a side that wants one.
pub(crate) fn space(a: Class, b: Class) -> bool {
    use Class::*;
    if matches!((a, b), (Brace, BraceClose) | (Number, DotNumber)) {
        return matches!(a, Number);
    }
    let none_after = matches!(
        a,
        Open | Tight
            | RowOpen
            | Dot
            | DotNumber
            | KeyDot
            | Prefix
            | Range
            | Rest
            | AngleOpen
            | BarOpen
            | StrOpen
            | StrMid
    );
    let none_before = matches!(
        b,
        Tight
            | Close
            | RowClose
            | Comma
            | Colon
            | Dot
            | DotNumber
            | Range
            | AngleOpen
            | AngleClose
            | BarClose
            | StrMid
            | StrClose
            | Format
    );
    if none_after || none_before {
        return false;
    }
    let after = matches!(a, Spaced | SpacedPrefix | Comma | Colon | Brace | BarClose);
    let before = matches!(b, Spaced | Brace | BraceClose | RowOpen);
    after || before || (wordish(a) && wordish(b))
}

/// The classes that stand where a word could, between which a space keeps two tokens apart.
fn wordish(class: Class) -> bool {
    use Class::*;
    matches!(
        class,
        Word | Number | Close | BraceClose | RowClose | AngleClose | StrOpen | StrClose | Format
    )
}

#[cfg(test)]
mod tests {
    use super::Class::*;
    use super::space;

    #[test]
    fn a_side_that_wants_no_space_wins() {
        assert!(!space(Spaced, Close));
        assert!(!space(Open, Brace));
        assert!(space(Comma, Word));
        assert!(!space(Word, Tight));
        assert!(space(Spaced, Open));
        assert!(!space(Brace, BraceClose));
        assert!(space(Number, DotNumber));
        assert!(!space(Number, Dot));
        assert!(!space(Word, DotNumber));
        assert!(space(AngleClose, Word));
        assert!(!space(BarOpen, BarClose));
    }
}
