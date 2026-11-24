//! Names and paths, and the names of fields that patterns and struct literals refer to.

use crate::SyntaxKind::{self, *};
use crate::parser::{Expected, Parser};

/// A name that a declaration or a binding introduces.
pub(super) fn name(p: &mut Parser<'_>, kind: SyntaxKind) {
    if p.at(kind) {
        let m = p.start();
        p.bump(kind);
        m.complete(p, NAME);
    } else {
        p.error_expecting(Expected::Form(if kind == UPPER_IDENT {
            "a name in upper case"
        } else {
            "a name"
        }));
    }
}

pub(super) fn lower_path(p: &mut Parser<'_>) {
    let m = p.start();
    if p.expect(LOWER_IDENT) {
        while p.eat(DOT) {
            if !p.expect(LOWER_IDENT) {
                break;
            }
        }
    }
    m.complete(p, PATH);
}

/// The path of a `use`: a namespace's name, then names of either case, since name resolution
/// tells a module from an item (program.what-use-binds).
pub(super) fn use_path(p: &mut Parser<'_>) {
    let m = p.start();
    if p.expect(LOWER_IDENT) {
        while p.eat(DOT) {
            if p.at(UPPER_IDENT) {
                p.bump(UPPER_IDENT);
            } else if !p.expect(LOWER_IDENT) {
                break;
            }
        }
    }
    m.complete(p, PATH);
}

/// A path that ends in an uppercase name: `T`, `m.T`, `Self` or `T.NAME`.
pub(super) fn upper_path(p: &mut Parser<'_>) {
    let m = p.start();
    match p.current() {
        UPPER_IDENT | SELF_TYPE_KW => p.bump_any(),
        LOWER_IDENT => {
            p.bump(LOWER_IDENT);
            loop {
                if !p.expect(DOT) {
                    break;
                }
                match p.current() {
                    LOWER_IDENT => p.bump(LOWER_IDENT),
                    UPPER_IDENT => {
                        p.bump(UPPER_IDENT);
                        break;
                    }
                    _ => {
                        p.error();
                        break;
                    }
                }
            }
        }
        _ => p.error(),
    }
    while p.eat(DOT) {
        if !p.expect(UPPER_IDENT) {
            break;
        }
    }
    m.complete(p, PATH);
}

/// A field's name, which refers to a field rather than declaring one.
pub(super) fn name_ref(p: &mut Parser<'_>) {
    if p.at(LOWER_IDENT) {
        let m = p.start();
        p.bump(LOWER_IDENT);
        m.complete(p, NAME_REF);
    } else {
        p.error();
    }
}
