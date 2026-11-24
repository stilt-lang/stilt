//! Statements and blocks.

use super::exprs::{Mode, expr, starts_expr};
use super::module::recover_to_separator;
use super::patterns::pattern;
use super::types::ty;
use crate::SyntaxKind::{self, *};
use crate::parser::{CompletedMarker, Expected, Parser};

pub(super) fn block(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.bump(L_CURLY);
    if !p.at(R_CURLY) {
        stmt(p);
        loop {
            match p.current() {
                R_CURLY | EOF => break,
                SEP => {
                    p.bump(SEP);
                    stmt(p);
                }
                _ => {
                    p.error();
                    recover_to_separator(p);
                }
            }
        }
    }
    p.expect(R_CURLY);
    m.complete(p, BLOCK)
}

pub(super) fn block_expected(p: &mut Parser<'_>) {
    if p.at(L_CURLY) {
        block(p);
    } else {
        p.error_expecting(Expected::Form("a block, in braces"));
    }
}

pub(super) fn stmt(p: &mut Parser<'_>) {
    let m = p.start();
    let kind = match p.current() {
        LET_KW | VAR_KW => {
            let kind = if p.at(LET_KW) { LET_STMT } else { VAR_STMT };
            p.bump_any();
            pattern(p);
            if p.eat(COLON) {
                ty(p);
            }
            p.expect(EQ);
            expr(p, Mode::Full);
            kind
        }
        ASSERT_KW => {
            p.bump(ASSERT_KW);
            expr(p, Mode::Full);
            ASSERT_STMT
        }
        // `yield e`, a statement of a projection's body (projections.yield).
        YIELD_KW => {
            p.bump(YIELD_KW);
            expr(p, Mode::Full);
            YIELD_STMT
        }
        kind if starts_expr(kind, Mode::Full) => {
            expr(p, Mode::Full);
            if is_assign_op(p.current()) {
                p.bump_any();
                expr(p, Mode::Full);
                ASSIGN_STMT
            } else {
                EXPR_STMT
            }
        }
        _ => {
            m.abandon(p);
            p.error();
            return;
        }
    };
    m.complete(p, kind);
}

pub(crate) fn is_assign_op(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        EQ | PLUS_EQ
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
    )
}
