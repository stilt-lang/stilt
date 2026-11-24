//! Effects and handlers (handlers.declaring-effect and handlers.handler-literals; tasks.async): an
//! effect's declaration and its operations, handler types and literals, `with` and `resume`.

use super::decls::{fn_decl, param_list};
use super::exprs::{Mode, expr};
use super::module::{docs, members};
use super::paths::{name, upper_path};
use super::stmts::block;
use super::types::{Args, row, ty, type_arg_list};
use crate::SyntaxKind::{self, *};
use crate::parser::Parser;

/// `effect Name<P…> { fn op(…) -> T / row … }` (handlers.declaring-effect). Its type parameters are
/// plain names, and its operations function heads without generics or bodies.
pub(super) fn effect_decl(p: &mut Parser<'_>) {
    p.bump(EFFECT_KW);
    name(p, UPPER_IDENT);
    if p.at(L_ANGLE) {
        effect_params(p);
    }
    if p.at(L_CURLY) {
        members(p, operation);
    } else {
        p.error();
    }
}

/// An effect's type parameters: uppercase names, separated by commas.
fn effect_params(p: &mut Parser<'_>) {
    let m = p.start();
    p.bump(L_ANGLE);
    loop {
        let param = p.start();
        name(p, UPPER_IDENT);
        param.complete(p, TYPE_PARAM);
        if !p.eat(COMMA) || p.at(R_ANGLE) {
            break;
        }
    }
    p.expect(R_ANGLE);
    m.complete(p, GENERIC_LIST);
}

/// An operation: its doc comments, `fn`, its name, parameters, result and row.
fn operation(p: &mut Parser<'_>) {
    let m = p.start();
    docs(p);
    if p.expect(FN_KW) {
        name(p, LOWER_IDENT);
        param_list(p);
        if p.at(THIN_ARROW) {
            let ret = p.start();
            p.bump(THIN_ARROW);
            ty(p);
            ret.complete(p, RET_TYPE);
        }
        if p.at(SLASH) {
            row(p);
        }
    }
    m.complete(p, OPERATION);
}

/// The effect a handler names: a path with its type arguments, or `async` (handlers.handler-types;
/// tasks.async).
fn effect_ref(p: &mut Parser<'_>) {
    if p.at(ASYNC_KW) {
        let m = p.start();
        p.bump(ASYNC_KW);
        m.complete(p, ROW_ASYNC);
    } else if matches!(p.current(), UPPER_IDENT | LOWER_IDENT | SELF_TYPE_KW) {
        let m = p.start();
        upper_path(p);
        if p.at(L_ANGLE) {
            type_arg_list(p, Args::Types);
        }
        m.complete(p, NAMED_TYPE);
    } else {
        p.error();
    }
}

/// A handler's result type, `-> R`, written for a handler that takes control (handlers.resuming).
fn answer(p: &mut Parser<'_>) {
    if p.at(THIN_ARROW) {
        let m = p.start();
        p.bump(THIN_ARROW);
        ty(p);
        m.complete(p, RET_TYPE);
    }
}

/// A handler type, `handler E -> R / row` (handlers.handler-types). Its `/` gives the row to the
/// innermost function or handler type that has none yet, as a function type's does.
pub(super) fn handler_type(p: &mut Parser<'_>) {
    let m = p.start();
    p.bump(HANDLER_KW);
    effect_ref(p);
    answer(p);
    if p.at(SLASH) {
        row(p);
    }
    m.complete(p, HANDLER_TYPE);
}

/// A handler literal, `handler E -> R { fn op(…) { … } … }` (handlers.handler-literals).
pub(super) fn handler_expr(p: &mut Parser<'_>) -> SyntaxKind {
    p.bump(HANDLER_KW);
    effect_ref(p);
    answer(p);
    if !p.expect(L_CURLY) {
        return HANDLER_EXPR;
    }
    if !p.at(R_CURLY) {
        loop {
            implementation(p);
            if !p.eat(SEP) {
                break;
            }
        }
    }
    p.expect(R_CURLY);
    HANDLER_EXPR
}

/// An operation's implementation in a handler literal: a function with a body.
fn implementation(p: &mut Parser<'_>) {
    let m = p.start();
    if p.at(FN_KW) {
        fn_decl(p);
    } else {
        p.error();
    }
    m.complete(p, FN);
}

/// `with h₁, h₂ { … }`, whose handlers are heads (handlers.with).
pub(super) fn with_expr(p: &mut Parser<'_>) -> SyntaxKind {
    p.bump(WITH_KW);
    loop {
        expr(p, Mode::Head);
        if !p.eat(COMMA) || p.at(L_CURLY) {
            break;
        }
    }
    if p.at(L_CURLY) {
        block(p);
    } else {
        p.error();
    }
    WITH_EXPR
}

/// `when a, b { … }`, whose names are each a `NAME_REF` (shared.when).
pub(super) fn when_expr(p: &mut Parser<'_>) -> SyntaxKind {
    p.bump(WHEN_KW);
    loop {
        if p.at(LOWER_IDENT) {
            let m = p.start();
            p.bump(LOWER_IDENT);
            m.complete(p, NAME_REF);
        } else {
            p.error();
            break;
        }
        if !p.eat(COMMA) || p.at(L_CURLY) {
            break;
        }
    }
    if p.at(L_CURLY) {
        block(p);
    } else {
        p.error();
    }
    WHEN_EXPR
}

/// `resume(v)` or `resume()` (handlers.resuming).
pub(super) fn resume_expr(p: &mut Parser<'_>) {
    p.bump(RESUME_KW);
    if p.expect(L_PAREN) {
        if !p.at(R_PAREN) {
            expr(p, Mode::Full);
        }
        p.expect(R_PAREN);
    }
}
