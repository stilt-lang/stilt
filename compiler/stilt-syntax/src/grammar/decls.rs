//! Declarations: functions, with their generics and parameters, types, traits and constants.

use super::exprs::{Mode, expr};
use super::lists::{comma_list, nonempty_comma_list};
use super::module::{docs, members};
use super::paths::{name, upper_path};
use super::stmts::block;
use super::types::{Args, fn_type, record_type, row, ty, type_arg_list};
use crate::SyntaxKind::*;
use crate::lexer::is_limit;
use crate::parser::Parser;

fn fn_head(p: &mut Parser<'_>) {
    p.bump(FN_KW);
    name(p, LOWER_IDENT);
    if p.at(L_ANGLE) {
        generic_list(p, Generics::Fn);
    }
    param_list(p);
    if p.at(THIN_ARROW) {
        let m = p.start();
        p.bump(THIN_ARROW);
        // A result written `inout T` makes the function a projection
        // (projections.declaring-projection); a function type has no such result
        // (`types::fn_type`).
        p.eat(INOUT_KW);
        ty(p);
        m.complete(p, RET_TYPE);
    }
    if p.at(SLASH) {
        row(p);
    }
}

/// A function with a body: its head, its `where` clause (traits.where), its limits
/// (declarations.limits) and its body.
pub(super) fn fn_decl(p: &mut Parser<'_>) {
    fn_head(p);
    if p.at(WHERE_KW) {
        where_clause(p);
    }
    if p.at_contextual(WITHOUT_KW) {
        limits(p);
    }
    fn_body(p, true);
}

/// A function written `extern`: a foreign function, whose head, or the `without` clause after it,
/// ends the item (c.foreign-functions and c.effects), or, after `pub`, one exported to C when a
/// `where` clause or a body follows (c.exported-functions). An `extern` without `pub` takes
/// neither, and a `where` clause can't follow a `without` clause.
pub(super) fn extern_decl(p: &mut Parser<'_>, public: bool) {
    fn_head(p);
    let limited = p.at_contextual(WITHOUT_KW);
    if limited {
        limits(p);
    }
    if !(p.at(WHERE_KW) || matches!(p.current(), L_CURLY | EQ)) {
        return;
    }
    if !public || (limited && p.at(WHERE_KW)) {
        p.error();
        return;
    }
    if p.at(WHERE_KW) {
        where_clause(p);
        if p.at_contextual(WITHOUT_KW) {
            limits(p);
        }
    }
    fn_body(p, true);
}

/// A procedural macro: a function's head written with `macro`, whose result is written, and whose
/// body is a block (macros.procedural-declarations). Its generics, its row, its `without` clause
/// and the types of its parameters and result are checked after parsing.
pub(super) fn macro_decl(p: &mut Parser<'_>) {
    p.bump(MACRO_KW);
    name(p, LOWER_IDENT);
    if p.at(L_ANGLE) {
        generic_list(p, Generics::Fn);
    }
    param_list(p);
    if !p.at(THIN_ARROW) {
        p.error();
        return;
    }
    let m = p.start();
    p.bump(THIN_ARROW);
    ty(p);
    m.complete(p, RET_TYPE);
    if p.at(SLASH) {
        row(p);
    }
    if p.at_contextual(WITHOUT_KW) {
        limits(p);
    }
    if p.at(L_CURLY) {
        block(p);
    } else {
        p.error();
    }
}

/// A `without` clause: the limits of a module header (program.header-limits) or of a function
/// (declarations.limits and declarations.function-declarations and declarations.parameters),
/// separated by commas. The grammar accepts every limit in either place (facts.spelling;
/// facts.without).
pub(super) fn limits(p: &mut Parser<'_>) {
    let m = p.start();
    p.bump_contextual(WITHOUT_KW);
    loop {
        // `unsafe`, a keyword, is a limit too (c.without-unsafe).
        if p.at(UNSAFE_KW) {
            p.bump(UNSAFE_KW);
        } else if let Some(limit) = p.nth_contextual(0).filter(|k| is_limit(*k)) {
            p.bump_contextual(limit);
        } else {
            p.error();
            break;
        }
        if !p.eat(COMMA) {
            break;
        }
    }
    m.complete(p, LIMITS);
}

/// A function's body: a block, or `= ?`. In a trait, a function may leave it out.
fn fn_body(p: &mut Parser<'_>, required: bool) {
    match p.current() {
        L_CURLY => {
            block(p);
        }
        EQ => {
            let m = p.start();
            p.bump(EQ);
            p.expect(QUESTION);
            m.complete(p, HOLE_BODY);
        }
        _ if required => p.error(),
        _ => {}
    }
}

/// The lists of generics that declarations take. Only functions declare row variables
/// (effects.row-variables), only functions and impl blocks take bounds (traits.bounds), and only
/// functions, types and impl blocks declare value parameters (generics.value-parameters and
/// generics.value-parameter-positions).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Generics {
    Fn,
    Impl,
    /// A polymorphic function type's, which are an impl block's but for packs, read so that
    /// they are reported after parsing (variadics.packs).
    FnType,
    Type,
    /// A trait's parameters, which are a type's but for value parameters (traits.trait-parameters).
    Trait,
}

impl Generics {
    /// Whether the list takes bounds after a type parameter's name.
    fn bounded(self) -> bool {
        !matches!(self, Generics::Type | Generics::Trait)
    }

    /// Whether the list may declare value parameters, `n: T` (generics.value-parameters).
    fn values(self) -> bool {
        matches!(self, Generics::Fn | Generics::Impl | Generics::Type)
    }
}

pub(super) fn generic_list(p: &mut Parser<'_>, generics: Generics) {
    let m = p.start();
    p.bump(L_ANGLE);
    loop {
        match p.current() {
            // A pack among a function's or a type's generics (variadics.packs); where it may
            // stand is decided after parsing.
            DOT2 if generics != Generics::Impl => {
                let param = p.start();
                p.bump(DOT2);
                name(p, UPPER_IDENT);
                if generics.bounded() && p.at(COLON) {
                    p.bump(COLON);
                    bound_list(p);
                }
                param.complete(p, TYPE_PARAM);
            }
            UPPER_IDENT => {
                let param = p.start();
                name(p, UPPER_IDENT);
                if generics.bounded() && p.at(COLON) {
                    p.bump(COLON);
                    bound_list(p);
                }
                param.complete(p, TYPE_PARAM);
            }
            // A lowercase generic with a type is a value parameter, and a function's without one
            // a row variable (syntax.lowercase-generics).
            LOWER_IDENT if generics.values() && (generics != Generics::Fn || p.nth(1) == COLON) => {
                let param = p.start();
                name(p, LOWER_IDENT);
                p.expect(COLON);
                ty(p);
                param.complete(p, VALUE_PARAM);
            }
            LOWER_IDENT if generics == Generics::Fn => {
                let param = p.start();
                name(p, LOWER_IDENT);
                param.complete(p, ROW_PARAM);
            }
            _ => {
                p.error();
                break;
            }
        }
        if !p.eat(COMMA) || p.at(R_ANGLE) {
            break;
        }
    }
    p.expect(R_ANGLE);
    m.complete(p, GENERIC_LIST);
}

/// The bounds of a type parameter or of a member type, after its `:`: traits, each with its
/// arguments if it is given them (traits.bound-arguments).
pub(super) fn bound_list(p: &mut Parser<'_>) {
    let bounds = p.start();
    bound(p);
    while p.eat(PLUS) {
        bound(p);
    }
    bounds.complete(p, BOUND_LIST);
}

/// A trait, as a bound or as the trait of an impl, with its arguments if it is given them, or
/// a record bound, written as a record type (records.record-bounds).
pub(super) fn bound(p: &mut Parser<'_>) {
    let m = p.start();
    if p.at(L_CURLY) {
        record_type(p);
    } else {
        upper_path(p);
        if p.at(L_ANGLE) {
            type_arg_list(p, Args::Types);
        }
    }
    m.complete(p, BOUND);
}

/// A `where` clause, which bounds member types (traits.where).
pub(super) fn where_clause(p: &mut Parser<'_>) {
    let m = p.start();
    p.bump(WHERE_KW);
    loop {
        let b = p.start();
        upper_path(p);
        p.expect(COLON);
        bound_list(p);
        b.complete(p, WHERE_BOUND);
        if !p.eat(COMMA) || !matches!(p.current(), UPPER_IDENT | LOWER_IDENT | SELF_TYPE_KW) {
            break;
        }
    }
    m.complete(p, WHERE_CLAUSE);
}

pub(super) fn param_list(p: &mut Parser<'_>) {
    let m = p.start();
    if p.expect(L_PAREN) {
        let self_first = p.at(SELF_KW) || (p.at(INOUT_KW) && p.nth(1) == SELF_KW);
        let rest = if self_first {
            let param = p.start();
            mode(p);
            p.bump(SELF_KW);
            // A receiver's written type, which a constructor trait's methods need
            // (traits.receiver-types).
            if p.eat(COLON) {
                ty(p);
            }
            param.complete(p, SELF_PARAM);
            p.eat(COMMA)
        } else {
            true
        };
        if rest {
            comma_list(p, R_PAREN, param);
        }
        p.expect(R_PAREN);
    }
    m.complete(p, PARAM_LIST);
}

/// A parameter. `escaping` is read as a keyword at the start of every parameter
/// (lexical.contextual-keywords.as-names), and an escaping parameter takes no mode and a type
/// written with `fn` (declarations.parameters).
fn param(p: &mut Parser<'_>) {
    let m = p.start();
    if p.at_contextual(ESCAPING_KW) {
        p.bump_contextual(ESCAPING_KW);
        name(p, LOWER_IDENT);
        p.expect(COLON);
        if p.at(FN_KW) {
            fn_type(p);
        } else {
            p.error();
        }
    } else {
        mode(p);
        name(p, LOWER_IDENT);
        p.expect(COLON);
        ty(p);
    }
    m.complete(p, PARAM);
}

pub(super) fn mode(p: &mut Parser<'_>) {
    p.eat(INOUT_KW);
}

pub(super) fn type_decl(p: &mut Parser<'_>) {
    p.bump(TYPE_KW);
    name(p, UPPER_IDENT);
    if p.at(L_ANGLE) {
        generic_list(p, Generics::Type);
    }
    if !p.expect(EQ) {
        return;
    }
    match p.current() {
        L_CURLY => {
            let m = p.start();
            p.bump(L_CURLY);
            comma_list(p, R_CURLY, |p| {
                let field = p.start();
                name(p, LOWER_IDENT);
                p.expect(COLON);
                ty(p);
                field.complete(p, FIELD_DEF);
            });
            p.expect(R_CURLY);
            m.complete(p, RECORD_DEF);
        }
        PIPE | UPPER_IDENT => variant_list(p),
        // A native type, which only the standard library declares (views.std-view).
        QUESTION => p.bump(QUESTION),
        _ => p.error(),
    }
}

/// The variants of a type. A single variant needs its leading `|` (declarations.variant-types).
fn variant_list(p: &mut Parser<'_>) {
    let m = p.start();
    if !p.eat(PIPE) {
        variant(p);
        p.expect(PIPE);
    }
    variant(p);
    while p.eat(PIPE) {
        variant(p);
    }
    m.complete(p, VARIANT_LIST);
}

fn variant(p: &mut Parser<'_>) {
    let m = p.start();
    name(p, UPPER_IDENT);
    if p.at(L_PAREN) {
        let payloads = p.start();
        p.bump(L_PAREN);
        nonempty_comma_list(p, R_PAREN, |p| {
            let payload = p.start();
            if p.at(LOWER_IDENT) && p.nth(1) == COLON {
                name(p, LOWER_IDENT);
                p.bump(COLON);
            }
            ty(p);
            payload.complete(p, PAYLOAD);
        });
        p.expect(R_PAREN);
        payloads.complete(p, PAYLOAD_LIST);
    }
    m.complete(p, VARIANT);
}

pub(super) fn trait_body(p: &mut Parser<'_>) {
    p.bump(TRAIT_KW);
    name(p, UPPER_IDENT);
    // A trait's parameters are plain names (traits.trait-parameters).
    if p.at(L_ANGLE) {
        generic_list(p, Generics::Trait);
    }
    if p.at(L_CURLY) {
        members(p, trait_member);
    } else {
        p.error();
    }
}

/// A function or a constant of a trait, with or without a default (traits.functions-without-self
/// and traits.trait-constants). A function with limits has a body (syntax.declarations).
pub(super) fn trait_member(p: &mut Parser<'_>) {
    let m = p.start();
    docs(p);
    if p.at(CONST_KW) {
        p.bump(CONST_KW);
        name(p, UPPER_IDENT);
        p.expect(COLON);
        ty(p);
        if p.eat(EQ) {
            expr(p, Mode::Full);
        }
        m.complete(p, CONST);
    } else if p.at(FN_KW) {
        fn_head(p);
        if p.at(WHERE_KW) {
            where_clause(p);
        }
        let limited = p.at_contextual(WITHOUT_KW);
        if limited {
            limits(p);
        }
        fn_body(p, limited);
        m.complete(p, FN);
    } else {
        p.error();
        m.complete(p, ERROR);
    }
}

pub(super) fn const_decl(p: &mut Parser<'_>) {
    p.bump(CONST_KW);
    name(p, UPPER_IDENT);
    p.expect(COLON);
    ty(p);
    p.expect(EQ);
    expr(p, Mode::Full);
}
