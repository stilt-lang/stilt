//! Quotes and their splices (macros.quote and macros.splices; syntax.quotes): a quote holds
//! a block, or after `type`, `pattern` or `field` one form of that kind in braces, inside which
//! `$` begins a splice, `$x` or `$(e)`, or a spread, `$..x` or `$..(e)`.

use super::exprs::{Mode, expr};
use super::patterns::pattern;
use super::stmts::block;
use super::types::ty;
use crate::SyntaxKind::{self, *};
use crate::parser::Parser;

/// A quote, after which the parser reads its contents as a quote's.
pub(super) fn quote_expr(p: &mut Parser<'_>) -> SyntaxKind {
    p.bump(QUOTE_KW);
    match p.current() {
        L_CURLY => {
            p.quoted(block);
        }
        TYPE_KW => {
            p.bump(TYPE_KW);
            braced(p, |p| {
                ty(p);
            });
        }
        LOWER_IDENT if p.at_contextual(PATTERN_KW) => {
            p.bump_contextual(PATTERN_KW);
            braced(p, pattern);
        }
        LOWER_IDENT if p.at_contextual(FIELD_KW) => {
            p.bump_contextual(FIELD_KW);
            braced(p, record_field);
        }
        _ => p.error(),
    }
    QUOTE_EXPR
}

/// One form in braces, read as a quote's contents.
fn braced(p: &mut Parser<'_>, form: impl FnOnce(&mut Parser<'_>)) {
    if !p.expect(L_CURLY) {
        return;
    }
    p.quoted(|p| {
        form(p);
        p.expect(R_CURLY);
    });
}

/// Whether the tokens under the cursor begin a spread of a quote, `$..`.
pub(super) fn at_spread(p: &Parser<'_>) -> bool {
    p.in_quote() && p.at(DOLLAR) && p.nth(1) == DOT2
}

/// Whether the cursor is at a splice of a quote, `$`.
pub(super) fn at_splice(p: &Parser<'_>) -> bool {
    p.in_quote() && p.at(DOLLAR)
}

/// A splice, `$x` or `$(e)`, in a node of `kind`: the name as a variable, or the expression in
/// parentheses.
pub(super) fn splice(p: &mut Parser<'_>, kind: SyntaxKind) {
    let m = p.start();
    p.bump(DOLLAR);
    spliced(p);
    m.complete(p, kind);
}

/// A splice's tokens, `$x` or `$(e)`, in the node of `kind` that the caller started.
pub(super) fn spliced_as(p: &mut Parser<'_>, kind: SyntaxKind) -> SyntaxKind {
    p.bump(DOLLAR);
    spliced(p);
    kind
}

/// A spread, `$..x` or `$..(e)`.
pub(super) fn spread(p: &mut Parser<'_>) {
    let m = p.start();
    p.bump(DOLLAR);
    p.bump(DOT2);
    spliced(p);
    m.complete(p, SPLICE_SPREAD);
}

/// What a splice or a spread names: a variable of the macro's code, or an expression of it in
/// parentheses.
pub(super) fn spliced(p: &mut Parser<'_>) {
    match p.current() {
        LOWER_IDENT => {
            let m = p.start();
            p.bump(LOWER_IDENT);
            m.complete(p, NAME_REF);
        }
        L_PAREN => {
            let m = p.start();
            p.bump(L_PAREN);
            expr(p, Mode::Full);
            p.expect(R_PAREN);
            m.complete(p, PAREN_EXPR);
        }
        _ => p.error(),
    }
}

/// Whether a `{` under the cursor begins a record literal of a quote, which a spread or a splice
/// and a `:` follow (macros.splices).
pub(super) fn at_spliced_record(p: &Parser<'_>) -> bool {
    if !p.in_quote() || p.nth(1) != DOLLAR {
        return false;
    }
    match p.nth(2) {
        DOT2 => true,
        LOWER_IDENT => p.nth(3) == COLON,
        L_PAREN => {
            let mut depth = 0_usize;
            let mut i = 2;
            loop {
                match p.nth(i) {
                    L_PAREN | L_BRACK | L_CURLY => depth += 1,
                    R_PAREN | R_BRACK | R_CURLY => {
                        depth -= 1;
                        if depth == 0 {
                            return p.nth(i + 1) == COLON;
                        }
                    }
                    EOF => return false,
                    _ => {}
                }
                i += 1;
            }
        }
        _ => false,
    }
}

/// A field of a record literal or a struct literal: `name: e`, `name`, or in a quote one that
/// a splice names, `$n: e`, or a spread of fields, `$..fs`.
pub(super) fn record_field(p: &mut Parser<'_>) {
    if at_spread(p) {
        spread(p);
        return;
    }
    let field = p.start();
    if at_splice(p) {
        splice(p, SPLICE_NAME);
        if p.expect(COLON) {
            expr(p, Mode::Full);
        }
    } else {
        super::paths::name_ref(p);
        if p.eat(COLON) {
            expr(p, Mode::Full);
        }
    }
    field.complete(p, FIELD_INIT);
}
