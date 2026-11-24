//! Control flow: `try` and its `catch`, `match`, the loops and `if`.

use super::decls::bound_list;
use super::exprs::{Mode, expr};
use super::paths::name;
use super::patterns::pattern;
use super::stmts::{block, block_expected};
use crate::SyntaxKind::{self, *};
use crate::parser::{CompletedMarker, Expected, Parser};

/// `try`, perhaps with a `catch`. A `catch` belongs to the innermost `try` whose operand is
/// still open, which is this one once its operand ends. Heads leave out the block form.
pub(super) fn try_expr(p: &mut Parser<'_>, mode: Mode) {
    p.bump(TRY_KW);
    expr(p, mode);
    if p.at(CATCH_KW) {
        let m = p.start();
        p.bump(CATCH_KW);
        if mode == Mode::Full && p.at(L_CURLY) && !record_pattern_follows(p) {
            arms(p, |p| catch_arm(p, Mode::Full));
        } else {
            catch_arm(p, mode);
        }
        m.complete(p, CATCH_CLAUSE);
    }
}

/// Whether the `{` after a `catch` opens the pattern of its one arm, an anonymous record's,
/// and not its block of arms: one that holds `..`, or whose first field's name a `:`, a `,` or
/// the `}` follows, as no arm's pattern is followed (records.anonymous-patterns).
fn record_pattern_follows(p: &Parser<'_>) -> bool {
    p.nth(1) == DOT2 || (p.nth(1) == LOWER_IDENT && matches!(p.nth(2), COLON | COMMA | R_CURLY))
}

/// An arm of a `catch`, which has a guard or a reason, never both. Its guard and its body are
/// of the grammar of the expression the `catch` is in.
fn catch_arm(p: &mut Parser<'_>, mode: Mode) {
    let m = p.start();
    pattern(p);
    if p.at(IF_KW) {
        let guard = p.start();
        p.bump(IF_KW);
        expr(p, mode);
        guard.complete(p, GUARD);
    } else if p.at_contextual(BECAUSE_KW) {
        let because = p.start();
        p.bump_contextual(BECAUSE_KW);
        p.expect(STRING);
        because.complete(p, BECAUSE);
    }
    p.expect(FAT_ARROW);
    expr(p, mode);
    m.complete(p, ARM);
}

fn match_arm(p: &mut Parser<'_>) {
    let m = p.start();
    pattern(p);
    if p.at(IF_KW) {
        let guard = p.start();
        p.bump(IF_KW);
        expr(p, Mode::Full);
        guard.complete(p, GUARD);
    }
    p.expect(FAT_ARROW);
    expr(p, Mode::Full);
    m.complete(p, ARM);
}

/// Arms between braces, separated by separators or commas, with an optional one at the end.
fn arms(p: &mut Parser<'_>, arm: impl Fn(&mut Parser<'_>)) {
    p.bump(L_CURLY);
    while !p.at(R_CURLY) && !p.at(EOF) {
        arm(p);
        if !p.eat(SEP) && !p.eat(COMMA) {
            break;
        }
    }
    p.expect(R_CURLY);
}

/// `match` and the loops, which heads leave out.
pub(super) fn control_flow(p: &mut Parser<'_>) -> SyntaxKind {
    match p.current() {
        MATCH_KW => {
            p.bump(MATCH_KW);
            expr(p, Mode::Head);
            if p.at(L_CURLY) {
                arms(p, match_arm);
            } else {
                p.error();
            }
            MATCH_EXPR
        }
        LOOP_KW => {
            p.bump(LOOP_KW);
            block_expected(p);
            LOOP_EXPR
        }
        WHILE_KW => {
            p.bump(WHILE_KW);
            expr(p, Mode::Head);
            block_expected(p);
            WHILE_EXPR
        }
        _ => {
            p.bump(FOR_KW);
            pattern(p);
            p.expect(IN_KW);
            let start = expr(p, Mode::Head);
            if matches!(p.current(), DOT2 | DOT2EQ) {
                let range = match start {
                    Some(start) => start.precede(p),
                    None => p.start(),
                };
                p.bump_any();
                expr(p, Mode::Head);
                range.complete(p, RANGE);
            }
            block_expected(p);
            FOR_EXPR
        }
    }
}

/// `if`, `if let` (expressions.if-let), or a bound test, `if T: Show` (meta.bound-tests). An `else`
/// directly after its block belongs to it (expressions.else-after-if).
pub(super) fn if_expr(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.bump(IF_KW);
    if p.eat(LET_KW) {
        pattern(p);
        p.expect(EQ);
        expr(p, Mode::Head);
    } else if p.at(UPPER_IDENT) && p.nth(1) == COLON {
        // A bound test's bounds end at the block, so it is the whole condition.
        let test = p.start();
        name(p, UPPER_IDENT);
        p.bump(COLON);
        bound_list(p);
        test.complete(p, BOUND_TEST);
    } else {
        expr(p, Mode::Head);
    }
    block_expected(p);
    if p.eat(ELSE_KW) {
        match p.current() {
            L_CURLY => {
                block(p);
            }
            IF_KW => {
                if_expr(p);
            }
            _ => p.error_expecting(Expected::Form("a block or `if` after `else`")),
        }
    }
    m.complete(p, IF_EXPR)
}
