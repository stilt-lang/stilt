//! Expressions: the binding powers of the operators, and the prefix, postfix and primary forms.

use super::control::{control_flow, if_expr, try_expr};
use super::lists::{Parenthesized, comma_list, parenthesized};
use super::macros::{at_macro_use, macro_use};
use super::paths::name;
use super::patterns::alternative;
use super::quotes::{at_splice, at_spliced_record, at_spread, quote_expr, record_field, splice};
use super::stmts::block;
use super::types::ty;
use crate::SyntaxKind::{self, *};
use crate::parser::{CompletedMarker, Expected, Parser};

/// The grammar an expression follows: the full one, or that of the heads of expressions.heads,
/// which leaves out every form that holds a `{` of its own outside parentheses and brackets.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Mode {
    Full,
    Head,
}

/// Whether a token can start an expression in `mode`.
pub(super) fn starts_expr(kind: SyntaxKind, mode: Mode) -> bool {
    matches!(
        kind,
        INT | FLOAT
            | STRING
            | STRING_HEAD
            | TRUE_KW
            | FALSE_KW
            | SELF_KW
            | SELF_TYPE_KW
            | QUESTION
            | DOT
            | L_PAREN
            | L_BRACK
            | LOWER_IDENT
            | UPPER_IDENT
            | MINUS
            | BANG
            | TRY_KW
            | RAISE_KW
            | RETURN_KW
            | BREAK_KW
            | CONTINUE_KW
            | PIPE
            | PIPE2
            | RESUME_KW
            | DOLLAR
    ) || (mode == Mode::Full
        && matches!(
            kind,
            L_CURLY
                | IF_KW
                | MATCH_KW
                | LOOP_KW
                | WHILE_KW
                | FOR_KW
                | HANDLER_KW
                | WITH_KW
                | WHEN_KW
                | UNSAFE_KW
                | COMPTIME_KW
                | QUOTE_KW
        ))
}

/// The binding power of a prefix operator, tighter than every binary operator.
const PREFIX: u8 = 22;

/// The binding powers of a binary operator, on its left and on its right, from the Reference's
/// precedence table. An operator that associates to the left binds more tightly on its right.
fn infix(kind: SyntaxKind) -> Option<(u8, u8)> {
    Some(match kind {
        ELSE_KW => (2, 2),
        PIPE2 => (4, 5),
        AMP2 => (6, 7),
        EQ2 | NEQ | L_ANGLE | LTEQ | R_ANGLE | GTEQ => (COMPARISON, COMPARISON + 1),
        PIPE => (10, 11),
        CARET => (12, 13),
        AMP => (14, 15),
        SHL | SHR => (16, 17),
        PLUS | MINUS | PLUS_PERCENT | MINUS_PERCENT => (18, 19),
        STAR | SLASH | PERCENT | STAR_PERCENT => (20, 21),
        _ => return None,
    })
}

/// The binding power of the comparisons, which don't chain.
const COMPARISON: u8 = 8;

pub(super) fn expr(p: &mut Parser<'_>, mode: Mode) -> Option<CompletedMarker> {
    expr_bp(p, mode, 0)
}

fn expr_bp(p: &mut Parser<'_>, mode: Mode, min: u8) -> Option<CompletedMarker> {
    let mut lhs = unary(p, mode)?;
    let mut comparison = false;
    loop {
        let op = p.current();
        let Some((left, right)) = infix(op) else {
            break;
        };
        if left < min {
            break;
        }
        if left == COMPARISON && comparison {
            p.error();
        }
        let m = lhs.precede(p);
        p.bump(op);
        expr_bp(p, mode, right);
        lhs = m.complete(
            p,
            if op == ELSE_KW {
                ELSE_EXPR
            } else {
                BINARY_EXPR
            },
        );
        comparison = left == COMPARISON;
    }
    Some(lhs)
}

/// The prefix forms, and the forms of level 14, whose operands read as far to the right as
/// they can (expressions.open-ended-forms).
fn unary(p: &mut Parser<'_>, mode: Mode) -> Option<CompletedMarker> {
    let m = p.start();
    let kind = match p.current() {
        MINUS | BANG => {
            p.bump_any();
            expr_bp(p, mode, PREFIX);
            PREFIX_EXPR
        }
        TRY_KW => {
            try_expr(p, mode);
            TRY_EXPR
        }
        RAISE_KW => {
            p.bump(RAISE_KW);
            expr(p, mode);
            RAISE_EXPR
        }
        RETURN_KW => {
            // `return` takes an operand whenever the next token can start one here.
            p.bump(RETURN_KW);
            if starts_expr(p.current(), mode) {
                expr(p, mode);
            }
            RETURN_EXPR
        }
        BREAK_KW => {
            p.bump(BREAK_KW);
            BREAK_EXPR
        }
        CONTINUE_KW => {
            p.bump(CONTINUE_KW);
            CONTINUE_EXPR
        }
        PIPE => {
            p.bump(PIPE);
            comma_list(p, PIPE, |p| {
                let param = p.start();
                closure_param_pattern(p);
                if p.eat(COLON) {
                    ty(p);
                }
                param.complete(p, CLOSURE_PARAM);
            });
            p.expect(PIPE);
            expr(p, mode);
            CLOSURE_EXPR
        }
        PIPE2 => {
            p.bump(PIPE2);
            expr(p, mode);
            CLOSURE_EXPR
        }
        RESUME_KW => {
            super::effects::resume_expr(p);
            RESUME_EXPR
        }
        _ => {
            m.abandon(p);
            return postfix(p, mode);
        }
    };
    Some(m.complete(p, kind))
}

/// The pattern of a closure's parameter, which is a name when it is `inout`
/// (expressions.inout-closure-parameters).
fn closure_param_pattern(p: &mut Parser<'_>) {
    if p.eat(INOUT_KW) {
        let m = p.start();
        name(p, LOWER_IDENT);
        m.complete(p, BIND_PAT);
    } else {
        alternative(p);
    }
}

/// A primary followed by fields, calls and indexes. A path of identifiers, such as `fs.read`,
/// is a name followed by fields.
fn postfix(p: &mut Parser<'_>, mode: Mode) -> Option<CompletedMarker> {
    let mut lhs = primary(p, mode)?;
    while matches!(p.current(), DOT | L_PAREN | L_BRACK) {
        let m = lhs.precede(p);
        let kind = match p.current() {
            DOT => {
                p.bump(DOT);
                // `await` is a keyword, read as a member's name after `.` (tasks.std-task), and
                // in a quote a splice may name the member (macros.splices).
                if matches!(p.current(), LOWER_IDENT | UPPER_IDENT | INT | AWAIT_KW) {
                    p.bump_any();
                } else if at_splice(p) {
                    splice(p, SPLICE_NAME);
                } else {
                    p.error();
                }
                FIELD_EXPR
            }
            L_PAREN => {
                let args = p.start();
                p.bump(L_PAREN);
                comma_list(p, R_PAREN, |p| {
                    let arg = p.start();
                    if p.at(DOT2) {
                        spread(p);
                    } else if at_spread(p) {
                        super::quotes::spread(p);
                    } else {
                        p.eat(INOUT_KW);
                        expr(p, Mode::Full);
                    }
                    arg.complete(p, ARG);
                });
                p.expect(R_PAREN);
                args.complete(p, ARG_LIST);
                CALL_EXPR
            }
            _ => {
                p.bump(L_BRACK);
                expr(p, Mode::Full);
                p.expect(R_BRACK);
                INDEX_EXPR
            }
        };
        lhs = m.complete(p, kind);
    }
    Some(lhs)
}

/// Whether the tokens under the cursor are a path of identifiers that ends in an uppercase
/// name followed by `{`, which starts a struct literal (expressions.struct-literals).
fn at_struct_path(p: &Parser<'_>) -> bool {
    let mut i = 0;
    while p.nth(i + 1) == DOT && matches!(p.nth(i + 2), LOWER_IDENT | UPPER_IDENT) {
        i += 2;
    }
    p.nth(i) == UPPER_IDENT && p.nth(i + 1) == L_CURLY
}

/// Whether a `{` begins an anonymous record literal or an update: followed by a field and its
/// `:`, or by `..`, and in a quote by a splice and its `:`, or by a spread; any other begins a
/// block (records.anonymous-literals and records.update; macros.splices).
fn at_record(p: &Parser<'_>) -> bool {
    p.nth(1) == DOT2 || (p.nth(1) == LOWER_IDENT && p.nth(2) == COLON) || at_spliced_record(p)
}

fn primary(p: &mut Parser<'_>, mode: Mode) -> Option<CompletedMarker> {
    let full = mode == Mode::Full;
    let m = p.start();
    let kind = match p.current() {
        INT | FLOAT | STRING | TRUE_KW | FALSE_KW => {
            p.bump_any();
            LITERAL
        }
        STRING_HEAD => {
            interpolated(p);
            INTERP
        }
        SELF_KW => {
            p.bump(SELF_KW);
            SELF_EXPR
        }
        SELF_TYPE_KW if full && p.nth(1) == L_CURLY => struct_literal(p),
        SELF_TYPE_KW => {
            p.bump(SELF_TYPE_KW);
            SELF_TYPE_EXPR
        }
        QUESTION => {
            p.bump(QUESTION);
            HOLE_EXPR
        }
        DOT => key_path(p),
        L_PAREN | L_BRACK => bracketed(p),
        // A splice of a quote, in a head too (macros.splices).
        DOLLAR if p.in_quote() => super::quotes::spliced_as(p, SPLICE_EXPR),
        // A use, whose trailing block a head leaves out (macros.uses).
        LOWER_IDENT if at_macro_use(p) => {
            macro_use(p, full);
            MACRO_USE
        }
        LOWER_IDENT | UPPER_IDENT if full && at_struct_path(p) => struct_literal(p),
        LOWER_IDENT | UPPER_IDENT => {
            p.bump_any();
            NAME_REF
        }
        L_CURLY if full && at_record(p) => {
            record_fields(p);
            RECORD_EXPR
        }
        L_CURLY | IF_KW if full => {
            m.abandon(p);
            return Some(if p.at(IF_KW) { if_expr(p) } else { block(p) });
        }
        MATCH_KW | LOOP_KW | WHILE_KW | FOR_KW if full => control_flow(p),
        HANDLER_KW if full => super::effects::handler_expr(p),
        WITH_KW if full => super::effects::with_expr(p),
        WHEN_KW if full => super::effects::when_expr(p),
        UNSAFE_KW if full => unsafe_expr(p),
        COMPTIME_KW if full => staged(p),
        QUOTE_KW if full => quote_expr(p),
        _ => {
            m.abandon(p);
            p.error_expecting(Expected::Form("an expression"));
            return None;
        }
    };
    Some(m.complete(p, kind))
}

/// `unsafe because "reason" { … }`, whose reason is a string with no interpolation
/// (c.unsafe-because). Heads leave it out, as they leave out a block.
fn unsafe_expr(p: &mut Parser<'_>) -> SyntaxKind {
    p.bump(UNSAFE_KW);
    if p.at_contextual(BECAUSE_KW) {
        let because = p.start();
        p.bump_contextual(BECAUSE_KW);
        p.expect(STRING);
        because.complete(p, BECAUSE);
        if p.at(L_CURLY) {
            block(p);
        } else {
            p.error();
        }
    } else {
        p.error();
    }
    UNSAFE_EXPR
}

/// A staging annotation: `comptime` before an `if`, a `match` or a `for`, and nothing else
/// (meta.staging-annotations). Heads leave it out.
fn staged(p: &mut Parser<'_>) -> SyntaxKind {
    p.bump(COMPTIME_KW);
    match p.current() {
        IF_KW => {
            if_expr(p);
        }
        MATCH_KW | FOR_KW => {
            let form = p.start();
            let kind = control_flow(p);
            form.complete(p, kind);
        }
        _ => p.error(),
    }
    COMPTIME_EXPR
}

/// The start of a key path: the `.` that starts it, and the name or the index after it.
fn key_path(p: &mut Parser<'_>) -> SyntaxKind {
    p.bump(DOT);
    if matches!(p.current(), LOWER_IDENT | INT) {
        p.bump_any();
    } else {
        p.error();
    }
    KEY_PATH_EXPR
}

/// An expression in parentheses, a tuple or a list. A spread makes a tuple even alone, as
/// `(..e)` (variadics.spread-expressions).
fn bracketed(p: &mut Parser<'_>) -> SyntaxKind {
    if p.at(L_PAREN) {
        p.bump(L_PAREN);
        let spread = p.at(DOT2) || at_spread(p);
        match parenthesized(p, element) {
            Parenthesized::One if !spread => PAREN_EXPR,
            _ => TUPLE_EXPR,
        }
    } else {
        p.bump(L_BRACK);
        comma_list(p, R_BRACK, element);
        p.expect(R_BRACK);
        LIST_EXPR
    }
}

/// An element of a tuple or a list: an expression, or a spread, of a pack or, in a quote, of a
/// list (macros.spreads).
fn element(p: &mut Parser<'_>) {
    if p.at(DOT2) {
        spread(p);
    } else if at_spread(p) {
        super::quotes::spread(p);
    } else {
        expr(p, Mode::Full);
    }
}

/// A spread, `..e`: of a pack tuple's elements (variadics.spread-expressions), or the base of an
/// update (records.update).
fn spread(p: &mut Parser<'_>) {
    let m = p.start();
    p.bump(DOT2);
    expr(p, Mode::Full);
    m.complete(p, SPREAD_EXPR);
}

/// A struct literal, whose path is `Self` or a path of identifiers.
fn struct_literal(p: &mut Parser<'_>) -> SyntaxKind {
    let path = p.start();
    p.bump_any();
    while p.at(DOT) {
        p.bump(DOT);
        p.bump_any();
    }
    path.complete(p, PATH);
    record_fields(p);
    STRUCT_EXPR
}

/// The fields of a struct literal or an anonymous record literal, after the base of an
/// update, if any (records.update-fields).
fn record_fields(p: &mut Parser<'_>) {
    p.bump(L_CURLY);
    if p.at(DOT2) {
        spread(p);
        if !p.eat(COMMA) {
            p.expect(R_CURLY);
            return;
        }
    }
    comma_list(p, R_CURLY, record_field);
    p.expect(R_CURLY);
}

fn interpolated(p: &mut Parser<'_>) {
    p.bump(STRING_HEAD);
    loop {
        let splice = p.start();
        expr(p, Mode::Full);
        p.eat(FORMAT);
        splice.complete(p, SPLICE);
        match p.current() {
            STRING_MID => p.bump(STRING_MID),
            STRING_TAIL => {
                p.bump(STRING_TAIL);
                break;
            }
            _ => {
                p.error();
                break;
            }
        }
    }
}
