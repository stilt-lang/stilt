//! The lists that rules of several sections read: elements separated by commas, and lists in
//! parentheses.

use crate::SyntaxKind::{self, *};
use crate::parser::Parser;

/// Elements separated by commas, perhaps with one at the end, up to `close`, which the caller
/// reads. There may be none.
pub(super) fn comma_list(p: &mut Parser<'_>, close: SyntaxKind, element: impl Fn(&mut Parser<'_>)) {
    while !p.at(close) {
        element(p);
        if !p.eat(COMMA) {
            p.hint_comma(close);
            break;
        }
    }
}

/// At least one element, separated by commas, perhaps with one at the end, up to `close`.
pub(super) fn nonempty_comma_list(
    p: &mut Parser<'_>,
    close: SyntaxKind,
    element: impl Fn(&mut Parser<'_>),
) {
    loop {
        element(p);
        if !p.eat(COMMA) {
            p.hint_comma(close);
            break;
        }
        if p.at(close) {
            break;
        }
    }
}

/// What a list in parentheses holds: one element with no comma after it, which only groups, or
/// anything else, which is a tuple (expressions.trailing-commas).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Parenthesized {
    One,
    Tuple,
}

/// The elements of a list in parentheses, whose `(` is read, and its `)`.
pub(super) fn parenthesized(
    p: &mut Parser<'_>,
    element: impl Fn(&mut Parser<'_>),
) -> Parenthesized {
    let mut count = 0;
    let mut trailing = false;
    while !p.at(R_PAREN) {
        element(p);
        count += 1;
        trailing = p.eat(COMMA);
        if !trailing {
            p.hint_comma(R_PAREN);
            break;
        }
    }
    p.expect(R_PAREN);
    if count == 1 && !trailing {
        Parenthesized::One
    } else {
        Parenthesized::Tuple
    }
}
