//! Patterns.

use super::lists::{Parenthesized, nonempty_comma_list, parenthesized};
use super::macros::{at_macro_use, macro_use};
use super::paths::{name, name_ref, upper_path};
use super::quotes::{at_splice, splice, spliced_as};
use crate::SyntaxKind::*;
use crate::parser::{CompletedMarker, Expected, Parser};

pub(super) fn pattern(p: &mut Parser<'_>) {
    let first = alternative(p);
    if p.at(PIPE) {
        let m = match first {
            Some(first) => first.precede(p),
            None => p.start(),
        };
        while p.eat(PIPE) {
            alternative(p);
        }
        m.complete(p, OR_PAT);
    }
}

/// A pattern without alternatives.
pub(super) fn alternative(p: &mut Parser<'_>) -> Option<CompletedMarker> {
    let m = p.start();
    let kind = match p.current() {
        UNDERSCORE => {
            p.bump(UNDERSCORE);
            WILDCARD_PAT
        }
        LOWER_IDENT if at_macro_use(p) => macro_pattern(p),
        // A splice of a quote (macros.splices).
        DOLLAR if p.in_quote() => spliced_as(p, SPLICE_PAT),
        LOWER_IDENT if p.nth(1) != DOT => {
            name(p, LOWER_IDENT);
            BIND_PAT
        }
        INT | STRING | TRUE_KW | FALSE_KW => {
            p.bump_any();
            LITERAL_PAT
        }
        MINUS => {
            p.bump(MINUS);
            p.expect(INT);
            LITERAL_PAT
        }
        LOWER_IDENT | UPPER_IDENT | SELF_TYPE_KW => {
            upper_path(p);
            match p.current() {
                L_PAREN => {
                    p.bump(L_PAREN);
                    nonempty_comma_list(p, R_PAREN, pattern);
                    p.expect(R_PAREN);
                    VARIANT_PAT
                }
                L_CURLY => {
                    record_pattern(p, false);
                    RECORD_PAT
                }
                _ => PATH_PAT,
            }
        }
        L_PAREN => {
            p.bump(L_PAREN);
            match parenthesized(p, pattern) {
                Parenthesized::One => PAREN_PAT,
                Parenthesized::Tuple => TUPLE_PAT,
            }
        }
        L_BRACK => {
            list_pattern(p);
            LIST_PAT
        }
        // An anonymous record's pattern, which names no type (records.anonymous-patterns).
        L_CURLY => {
            record_pattern(p, true);
            RECORD_PAT
        }
        _ => {
            m.abandon(p);
            p.error_expecting(Expected::Form("a pattern"));
            return None;
        }
    };
    Some(m.complete(p, kind))
}

/// A use, which takes no trailing block in a pattern (macros.uses).
fn macro_pattern(p: &mut Parser<'_>) -> crate::SyntaxKind {
    macro_use(p, false);
    MACRO_PAT
}

/// A record's pattern. An anonymous record's names a field or holds `..`, since the record
/// has a field (records.anonymous-patterns), so `{}` is none.
fn record_pattern(p: &mut Parser<'_>, anonymous: bool) {
    p.bump(L_CURLY);
    if anonymous && p.at(R_CURLY) {
        p.error();
    }
    loop {
        if p.at(R_CURLY) {
            break;
        }
        if p.at(DOT2) {
            let rest = p.start();
            p.bump(DOT2);
            rest.complete(p, REST_PAT);
            p.eat(COMMA);
            break;
        }
        let field = p.start();
        // In a quote, a splice may name the field (macros.splices).
        if at_splice(p) {
            splice(p, SPLICE_NAME);
        } else {
            name_ref(p);
        }
        if p.eat(COLON) {
            pattern(p);
        }
        field.complete(p, FIELD_PAT);
        if !p.eat(COMMA) {
            break;
        }
    }
    p.expect(R_CURLY);
}

fn list_pattern(p: &mut Parser<'_>) {
    p.bump(L_BRACK);
    loop {
        if p.at(R_BRACK) {
            break;
        }
        if p.at(DOT2) {
            let rest = p.start();
            p.bump(DOT2);
            if p.at(LOWER_IDENT) {
                name(p, LOWER_IDENT);
            }
            rest.complete(p, REST_PAT);
            p.eat(COMMA);
            break;
        }
        pattern(p);
        if !p.eat(COMMA) {
            break;
        }
    }
    p.expect(R_BRACK);
}
