//! Programs: a file, its header and its items, impl blocks among them.

use super::decls::{
    Generics, const_decl, extern_decl, fn_decl, generic_list, limits, macro_decl, trait_body,
    type_decl, where_clause,
};
use super::effects::effect_decl;
use super::macros::syntax_decl;
use super::paths::{lower_path, use_path};
use super::stmts::block_expected;
use super::types::ty;
use crate::SyntaxKind::{self, *};
use crate::parser::{Expected, Parser};

pub(super) fn file(p: &mut Parser<'_>) {
    let m = p.start();
    contents(p);
    m.complete(p, SOURCE_FILE);
}

/// A file's header and items, or the items of a part of it (program.syntax-errors-at-run), up to
/// the end of the input.
pub(super) fn contents(p: &mut Parser<'_>) {
    if p.at(MODULE_KW) {
        header(p);
        if p.eat(SEP) {
            items(p);
        } else if !p.at(EOF) {
            p.error();
        }
    } else if !p.at(EOF) {
        items(p);
    }
    while !p.at(EOF) {
        p.skip_until(&[]);
        if !p.at(EOF) {
            let error = p.start();
            p.bump_any();
            error.complete(p, ERROR);
        }
    }
}

/// A module header: its path, and its `without` clauses, each on the line before it, on the next,
/// where no separator ends the line (lexical.terminator-insertion), or after a `;`
/// (program.header-limits).
fn header(p: &mut Parser<'_>) {
    let m = p.start();
    p.bump(MODULE_KW);
    lower_path(p);
    loop {
        if p.at(SEP) && p.nth_contextual(1) == Some(WITHOUT_KW) {
            p.bump(SEP);
        } else if !p.at_contextual(WITHOUT_KW) {
            break;
        }
        limits(p);
    }
    m.complete(p, HEADER);
}

/// Items separated by separators, up to the end of the input. At least one is read.
pub(super) fn items(p: &mut Parser<'_>) {
    loop {
        item(p);
        match p.current() {
            EOF => break,
            SEP => p.bump(SEP),
            _ => {
                p.error();
                recover_to_separator(p);
                if !p.eat(SEP) {
                    break;
                }
            }
        }
    }
}

/// Reads the rest of a statement or an item that has an error into error nodes, up to the next
/// separator outside brackets, a `}` that closes an enclosing block, or the end of the input.
pub(super) fn recover_to_separator(p: &mut Parser<'_>) {
    loop {
        p.skip_until(&[SEP]);
        if matches!(p.current(), R_PAREN | R_BRACK) {
            let m = p.start();
            p.bump_any();
            m.complete(p, ERROR);
        } else {
            break;
        }
    }
}

pub(super) fn is_item_start(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        USE_KW
            | IMPL_KW
            | DOC
            | PUB_KW
            | EXTERN_KW
            | FN_KW
            | TYPE_KW
            | TRAIT_KW
            | CONST_KW
            | TEST_KW
            | SYNTAX_KW
            | EFFECT_KW
            | MACRO_KW
    )
}

pub(super) fn item(p: &mut Parser<'_>) {
    match p.current() {
        USE_KW => {
            let m = p.start();
            p.bump(USE_KW);
            use_path(p);
            m.complete(p, USE);
        }
        // `meta use a.b`, `meta` being a word of the grammar only before `use` at the start of
        // an item (macros.meta-use).
        LOWER_IDENT if p.at_contextual(META_KW) => {
            let m = p.start();
            p.bump_contextual(META_KW);
            if p.expect(USE_KW) {
                use_path(p);
            }
            m.complete(p, USE);
        }
        IMPL_KW => impl_item(p),
        DOC | PUB_KW | EXTERN_KW | FN_KW | TYPE_KW | TRAIT_KW | CONST_KW | TEST_KW | SYNTAX_KW
        | EFFECT_KW | MACRO_KW => {
            declaration(p);
        }
        _ => p.error_expecting(Expected::Form(
            "a declaration, such as `fn`, `type` or `use`",
        )),
    }
}

/// A declaration of a module, with its doc comments, its `pub`, and the `extern` of a function
/// that a C program calls (c.exported-functions) or that C gives (c.foreign-functions).
fn declaration(p: &mut Parser<'_>) {
    let m = p.start();
    docs(p);
    if p.at(TEST_KW) {
        p.bump(TEST_KW);
        p.expect(STRING);
        block_expected(p);
        m.complete(p, TEST);
        return;
    }
    let public = p.eat(PUB_KW);
    let external = p.eat(EXTERN_KW);
    let kind = match p.current() {
        FN_KW if external => {
            extern_decl(p, public);
            FN
        }
        FN_KW => {
            fn_decl(p);
            FN
        }
        _ if external => {
            p.error();
            ERROR
        }
        TYPE_KW => {
            type_decl(p);
            TYPE_DECL
        }
        TRAIT_KW => {
            trait_body(p);
            TRAIT
        }
        CONST_KW => {
            const_decl(p);
            CONST
        }
        SYNTAX_KW => {
            syntax_decl(p);
            SYNTAX
        }
        EFFECT_KW => {
            effect_decl(p);
            EFFECT
        }
        // A procedural macro is a function's node, written with `macro`
        // (macros.procedural-declarations).
        MACRO_KW => {
            macro_decl(p);
            FN
        }
        _ => {
            p.error();
            ERROR
        }
    };
    m.complete(p, kind);
}

pub(super) fn docs(p: &mut Parser<'_>) {
    if p.at(DOC) {
        let m = p.start();
        p.bump(DOC);
        m.complete(p, DOCS);
    }
}

fn impl_item(p: &mut Parser<'_>) {
    let m = p.start();
    p.bump(IMPL_KW);
    if p.at(L_ANGLE) {
        generic_list(p, Generics::Impl);
    }
    let named = ty(p);
    let of_trait = p.at(FOR_KW);
    if of_trait {
        // Only a path, with its arguments, can name a trait.
        if !named {
            p.error();
        }
        p.bump(FOR_KW);
        ty(p);
    }
    if p.at(WHERE_KW) {
        where_clause(p);
    }
    if p.at(L_CURLY) {
        members(p, |p| impl_member(p, of_trait));
    } else {
        p.error();
    }
    m.complete(p, IMPL);
}

/// The members of an impl or a trait, between braces and separated by separators.
pub(super) fn members(p: &mut Parser<'_>, member: impl Fn(&mut Parser<'_>)) {
    p.bump(L_CURLY);
    if !p.at(R_CURLY) {
        member(p);
        loop {
            match p.current() {
                R_CURLY | EOF => break,
                SEP => {
                    p.bump(SEP);
                    member(p);
                }
                _ => {
                    p.error();
                    recover_to_separator(p);
                }
            }
        }
    }
    p.expect(R_CURLY);
}

/// A member of an impl: a function or a constant, either one public in an inherent impl. The
/// members of a trait impl take no `pub` (program.visibility), and its constants are the trait's
/// (traits.impl-members).
pub(super) fn impl_member(p: &mut Parser<'_>, of_trait: bool) {
    let m = p.start();
    docs(p);
    if !of_trait {
        p.eat(PUB_KW);
    }
    let kind = match p.current() {
        FN_KW => {
            fn_decl(p);
            FN
        }
        CONST_KW => {
            const_decl(p);
            CONST
        }
        _ => {
            p.error();
            ERROR
        }
    };
    m.complete(p, kind);
}
