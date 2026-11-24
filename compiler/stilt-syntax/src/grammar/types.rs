//! Types and rows.

use super::decls::{Generics, generic_list, mode};
use super::lists::{Parenthesized, comma_list, parenthesized};
use super::paths::{name, upper_path};
use crate::SyntaxKind::*;
use crate::parser::{Expected, Parser};

/// A type. Tells whether it is a path to a type, with or without type arguments, which is all
/// that can name a trait with its arguments (traits.trait-arguments).
pub(super) fn ty(p: &mut Parser<'_>) -> bool {
    match p.current() {
        // A use of a procedural macro whose result is a type, which takes no trailing block,
        // and in a quote a splice (macros.splices and macros.procedural-uses).
        LOWER_IDENT if super::macros::at_macro_use(p) => {
            let m = p.start();
            super::macros::macro_use(p, false);
            m.complete(p, MACRO_TYPE);
            false
        }
        DOLLAR if p.in_quote() => {
            super::quotes::splice(p, SPLICE_TYPE);
            false
        }
        LOWER_IDENT if p.nth(1) != DOT => {
            let m = p.start();
            let path = p.start();
            p.bump(LOWER_IDENT);
            path.complete(p, PATH);
            m.complete(p, NAMED_TYPE);
            false
        }
        LOWER_IDENT | UPPER_IDENT | SELF_TYPE_KW => {
            let m = p.start();
            upper_path(p);
            if p.at(L_ANGLE) {
                type_arg_list(p, Args::Values);
            }
            m.complete(p, NAMED_TYPE);
            true
        }
        L_PAREN => {
            let m = p.start();
            p.bump(L_PAREN);
            // A spread makes a tuple even alone, as `(..Ts)` (variadics.type-spreads).
            let spread = p.at(DOT2);
            let kind = parenthesized(p, elem_type);
            m.complete(
                p,
                if kind == Parenthesized::One && !spread {
                    PAREN_TYPE
                } else {
                    TUPLE_TYPE
                },
            );
            false
        }
        L_CURLY => {
            record_type(p);
            false
        }
        FN_KW => {
            fn_type(p);
            false
        }
        HANDLER_KW => {
            super::effects::handler_type(p);
            false
        }
        _ => {
            p.error_expecting(Expected::Form("a type"));
            false
        }
    }
}

/// An element of a tuple type or a parameter of a function type: a type, or a spread `..T`
/// (variadics.type-spreads).
fn elem_type(p: &mut Parser<'_>) {
    if p.at(DOT2) {
        let m = p.start();
        p.bump(DOT2);
        ty(p);
        m.complete(p, SPREAD_TYPE);
    } else {
        ty(p);
    }
}

/// An anonymous record type, `{ f: T }`, or an open one, `{ f: T, .. }`, which also writes a record
/// bound (records.anonymous-types, records.record-bounds and records.open-parameter-types). Where
/// each may stand is decided after parsing.
pub(super) fn record_type(p: &mut Parser<'_>) {
    let m = p.start();
    p.bump(L_CURLY);
    loop {
        let field = p.start();
        name(p, LOWER_IDENT);
        p.expect(COLON);
        ty(p);
        field.complete(p, FIELD_DEF);
        if !p.eat(COMMA) || p.at(R_CURLY) {
            break;
        }
        if p.eat(DOT2) {
            break;
        }
    }
    p.expect(R_CURLY);
    m.complete(p, RECORD_TYPE);
}

/// Whether a list of type arguments may hold value arguments: a named type's may, and a
/// trait's or an effect's take types only (generics.value-arguments).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Args {
    Types,
    Values,
}

/// The type arguments of a named type, or of a trait or an effect. One `>>` may close this list
/// and the one around it (syntax.closing-angle-brackets).
pub(super) fn type_arg_list(p: &mut Parser<'_>, args: Args) {
    let m = p.start();
    p.bump(L_ANGLE);
    loop {
        if args == Args::Values && matches!(p.current(), MINUS | INT | TRUE_KW | FALSE_KW) {
            value_arg(p);
        } else {
            ty(p);
        }
        if !p.eat(COMMA) || p.at_closing_angle() {
            break;
        }
    }
    p.expect_closing_angle();
    m.complete(p, TYPE_ARG_LIST);
}

/// A literal value argument: an integer with an optional `-`, `true` or `false`
/// (generics.value-arguments and generics.value-argument-names). A name given for a value parameter
/// is read as a type, and told apart after parsing.
fn value_arg(p: &mut Parser<'_>) {
    let m = p.start();
    if p.eat(MINUS) {
        p.expect(INT);
    } else {
        p.bump_any();
    }
    m.complete(p, VALUE_ARG);
}

/// A function type. Its `/` gives a row to the innermost function type that has none yet
/// (declarations.function-type-rows), so a function type that is the return type takes the first
/// `/`. Its generics, if any, are type parameters with bounds, never row variables
/// (polymorphism.function-types).
pub(super) fn fn_type(p: &mut Parser<'_>) {
    let m = p.start();
    p.bump(FN_KW);
    if p.at(L_ANGLE) {
        generic_list(p, Generics::FnType);
    }
    let params = p.start();
    if p.expect(L_PAREN) {
        comma_list(p, R_PAREN, |p| {
            let param = p.start();
            if p.at(DOT2) {
                elem_type(p);
            } else {
                mode(p);
                ty(p);
            }
            param.complete(p, PARAM_TYPE);
        });
        p.expect(R_PAREN);
    }
    params.complete(p, PARAM_TYPE_LIST);
    if p.at(THIN_ARROW) {
        let ret = p.start();
        p.bump(THIN_ARROW);
        ty(p);
        ret.complete(p, RET_TYPE);
    }
    if p.at(SLASH) {
        row(p);
    }
    m.complete(p, FN_TYPE);
}

/// A row: one element, or a list of them in braces. In a row, `io` is the label, any other
/// lowercase name a row variable (effects.row-variables), an uppercase path an effect with its type
/// arguments (handlers.effects-in-rows), and `async` the effect of tasks (tasks.async).
pub(super) fn row(p: &mut Parser<'_>) {
    let m = p.start();
    p.bump(SLASH);
    if p.eat(L_CURLY) {
        comma_list(p, R_CURLY, row_element);
        p.expect(R_CURLY);
    } else {
        row_element(p);
    }
    m.complete(p, ROW);
}

fn row_element(p: &mut Parser<'_>) {
    let m = p.start();
    let kind = if p.at_contextual(IO_KW) {
        p.bump_contextual(IO_KW);
        ROW_IO
    } else if p.at(ASYNC_KW) {
        p.bump(ASYNC_KW);
        ROW_ASYNC
    } else if p.at(LOWER_IDENT) && p.nth(1) != DOT {
        p.bump(LOWER_IDENT);
        ROW_VAR
    } else if matches!(p.current(), UPPER_IDENT | LOWER_IDENT | SELF_TYPE_KW) {
        upper_path(p);
        if p.at(L_ANGLE) {
            type_arg_list(p, Args::Types);
        }
        ROW_EFFECT
    } else if p.at(RAISE_KW) {
        p.bump(RAISE_KW);
        if p.expect(L_ANGLE) {
            ty(p);
            p.expect_closing_angle();
        }
        ROW_RAISE
    } else {
        m.abandon(p);
        p.error();
        return;
    };
    m.complete(p, kind);
}
