//! What a keyword is, for semantic highlighting: `true` and `false` are booleans, `self` and
//! `Self` the receiver and its type, the built-in effects where they act as keywords are effects of
//! the library (lexical.contextual-keywords; effects.effect-names; facts.capabilities;
//! tasks.async), and the keywords that direct control, a branch, a loop, a jump, a failure or a
//! handler's, are marked as such, apart from those that declare, bind or annotate.

use stilt_lsp::TokenSort;
use stilt_lsp::modifier::{CONTROL_FLOW, LIBRARY};
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::SyntaxToken;

use super::super::syntax::is_keyword;
use super::control::CONTROL;

/// What a token is when it is a keyword, with its modifiers, and `None` when it isn't one.
pub(super) fn keyword(token: &SyntaxToken) -> Option<(TokenSort, u32)> {
    let kind = token.kind();
    let in_row = matches!(kind, RAISE_KW | ASYNC_KW | IO_KW)
        && token
            .parent()
            .is_some_and(|p| matches!(p.kind(), ROW_RAISE | ROW_ASYNC | ROW_IO));
    Some(match kind {
        TRUE_KW | FALSE_KW => (TokenSort::Boolean, 0),
        SELF_KW | SELF_TYPE_KW => (TokenSort::SelfKeyword, 0),
        // A limit or a capability, `locks`, `io`, or `raise` and `async` in a row.
        _ if (PANIC_KW..=LOCKS_KW).contains(&kind) || kind == IO_KW || in_row => {
            (TokenSort::Effect, LIBRARY)
        }
        // The `for` of `impl Trait for Type` declares.
        FOR_KW if token.parent().is_some_and(|p| p.kind() == IMPL) => (TokenSort::Keyword, 0),
        _ if CONTROL.iter().any(|(k, _)| *k == kind) => (TokenSort::Keyword, CONTROL_FLOW),
        _ if is_keyword(kind) => (TokenSort::Keyword, 0),
        _ => return None,
    })
}

/// What a keyword is that a doc example writes, whose code the tree doesn't parse
/// (tests.prop-lines).
pub(super) fn word(word: &str) -> (TokenSort, u32) {
    match word {
        "true" | "false" => (TokenSort::Boolean, 0),
        "self" | "Self" => (TokenSort::SelfKeyword, 0),
        _ if CONTROL.iter().any(|(_, w)| *w == word) => (TokenSort::Keyword, CONTROL_FLOW),
        _ => (TokenSort::Keyword, 0),
    }
}
