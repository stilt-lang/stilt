//! Macros (macros.syntax-declarations and macros.uses): a `syntax` declaration, with the matchers
//! of its patterns and the items of its templates, and a use, whose groups are read as balanced
//! tokens (syntax.macros).

use super::module::members;
use super::paths::name;
use crate::SyntaxKind::{self, *};
use crate::parser::Parser;

/// A `syntax` declaration, after its doc comments and its `pub` (macros.syntax-declarations).
pub(super) fn syntax_decl(p: &mut Parser<'_>) {
    p.bump(SYNTAX_KW);
    name(p, LOWER_IDENT);
    if p.at(L_CURLY) {
        members(p, arm);
    } else {
        p.error();
    }
}

/// An arm: a pattern's group, an optional trailing block, `=>` and a template (macros.patterns and
/// macros.templates).
fn arm(p: &mut Parser<'_>) {
    let m = p.start();
    if matches!(p.current(), L_PAREN | L_BRACK) {
        group(p, matcher);
        if p.at(DOLLAR) {
            let frag = p.start();
            p.bump(DOLLAR);
            if p.expect(LOWER_IDENT) && p.expect(COLON) {
                p.expect(LOWER_IDENT);
            }
            frag.complete(p, MACRO_FRAG);
        }
        if p.expect(FAT_ARROW) {
            template(p);
        }
    } else {
        p.error();
    }
    m.complete(p, MACRO_ARM);
}

/// Whether a token is a `TOKEN` of the grammar: any token but a bracket, `$` and a separator.
fn is_plain(kind: SyntaxKind) -> bool {
    !matches!(
        kind,
        L_PAREN
            | R_PAREN
            | L_BRACK
            | R_BRACK
            | L_CURLY
            | R_CURLY
            | DOLLAR
            | SEP
            | EOF
            | DOC
            | MISPLACED_DOC
    )
}

/// The closing bracket of an opening one.
fn closer(open: SyntaxKind) -> SyntaxKind {
    match open {
        L_PAREN => R_PAREN,
        L_BRACK => R_BRACK,
        _ => R_CURLY,
    }
}

/// A group, `( … )`, `[ … ]` or `{ … }`, of elements and separators.
fn group(p: &mut Parser<'_>, element: fn(&mut Parser<'_>)) {
    let m = p.start();
    let close = closer(p.current());
    p.bump_any();
    loop {
        match p.current() {
            kind if kind == close => break,
            SEP => sep(p),
            kind if is_plain(kind) || matches!(kind, DOLLAR | L_PAREN | L_BRACK | L_CURLY) => {
                element(p);
            }
            _ => break,
        }
    }
    p.expect(close);
    m.complete(p, MACRO_GROUP);
}

/// A separator inside a group, in a node of its own, since the tree keeps a newline that
/// separates as trivia.
fn sep(p: &mut Parser<'_>) {
    let m = p.start();
    p.bump(SEP);
    m.complete(p, MACRO_SEP);
}

/// A matcher of a pattern: a fragment, a repetition, a group or another token.
fn matcher(p: &mut Parser<'_>) {
    match p.current() {
        DOLLAR if p.nth(1) == L_PAREN => repetition(p, matcher),
        DOLLAR => {
            let m = p.start();
            p.bump(DOLLAR);
            if p.expect(LOWER_IDENT) && p.expect(COLON) {
                if matches!(p.current(), LOWER_IDENT | UPPER_IDENT | TYPE_KW) {
                    p.bump_any();
                } else {
                    p.error();
                }
            }
            m.complete(p, MACRO_FRAG);
        }
        L_PAREN | L_BRACK | L_CURLY => group(p, matcher),
        _ => p.bump_any(),
    }
}

/// A repetition, `$( … ) sep op`, of matchers or of a template's items.
fn repetition(p: &mut Parser<'_>, element: fn(&mut Parser<'_>)) {
    let m = p.start();
    p.bump(DOLLAR);
    group(p, element);
    match p.current() {
        COMMA => p.bump(COMMA),
        SEP => sep(p),
        _ => {}
    }
    if matches!(p.current(), STAR | PLUS) {
        p.bump_any();
    } else {
        p.error();
    }
    m.complete(p, MACRO_REP);
}

/// A template: its items up to the separator that ends the arm.
fn template(p: &mut Parser<'_>) {
    let m = p.start();
    let mut any = false;
    while is_plain(p.current()) || matches!(p.current(), DOLLAR | L_PAREN | L_BRACK | L_CURLY) {
        template_item(p);
        any = true;
    }
    if !any {
        p.error();
    }
    m.complete(p, TEMPLATE);
}

/// An item of a template: a fragment, a repetition, a group or another token.
fn template_item(p: &mut Parser<'_>) {
    match p.current() {
        DOLLAR if p.nth(1) == L_PAREN => repetition(p, template_item),
        DOLLAR => {
            let m = p.start();
            p.bump(DOLLAR);
            p.expect(LOWER_IDENT);
            m.complete(p, MACRO_FRAG);
        }
        L_PAREN | L_BRACK | L_CURLY => group(p, template_item),
        _ => p.bump_any(),
    }
}

/// Whether the tokens under the cursor begin a use: a path of lowercase names and `!`
/// (macros.uses).
pub(super) fn at_macro_use(p: &Parser<'_>) -> bool {
    if p.current() != LOWER_IDENT {
        return false;
    }
    let mut i = 0;
    while p.nth(i + 1) == DOT && p.nth(i + 2) == LOWER_IDENT {
        i += 2;
    }
    p.nth(i + 1) == BANG
}

/// A use's path, `!` and group, whose tokens are read as balanced tokens, and with
/// `trailing`, a `{ … }` group after it (macros.uses).
pub(super) fn macro_use(p: &mut Parser<'_>, trailing: bool) {
    let path = p.start();
    p.bump(LOWER_IDENT);
    while p.at(DOT) {
        p.bump(DOT);
        p.bump(LOWER_IDENT);
    }
    path.complete(p, PATH);
    p.bump(BANG);
    if matches!(p.current(), L_PAREN | L_BRACK) {
        group(p, token);
        if trailing && p.at(L_CURLY) {
            group(p, token);
        }
    } else {
        p.error();
    }
}

/// A token of a use's group, or a group of them. `$` stands only in a declaration
/// (macros.templates).
fn token(p: &mut Parser<'_>) {
    match p.current() {
        L_PAREN | L_BRACK | L_CURLY => group(p, token),
        DOLLAR => {
            p.error();
            p.bump_any();
        }
        _ => p.bump_any(),
    }
}
