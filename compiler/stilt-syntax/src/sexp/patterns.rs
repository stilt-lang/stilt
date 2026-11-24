//! The tree form of patterns.

use super::types::ty;
use super::{Sexp, atom, list, name, path, string, tagged};
use crate::SyntaxKind::*;
use crate::ast;
use crate::text::number_text;

pub(super) fn pattern(p: Option<ast::Pattern>) -> Sexp {
    let Some(p) = p else { return list([]) };
    match p {
        ast::Pattern::WildcardPat(_) => atom("_"),
        ast::Pattern::BindPat(b) => name(b.name()),
        ast::Pattern::LiteralPat(l) => match l.literal() {
            Some(t) if t.kind() == STRING => string(&t),
            Some(t) if t.kind() == INT => atom(format!(
                "{}{}",
                if l.is_negative() { "-" } else { "" },
                number_text(&t)
            )),
            Some(t) => atom(t.text()),
            None => list([]),
        },
        ast::Pattern::PathPat(p) => path(p.path()),
        ast::Pattern::VariantPat(v) => {
            list(std::iter::once(path(v.path())).chain(v.patterns().map(|p| pattern(Some(p)))))
        }
        ast::Pattern::RecordPat(r) => {
            let fields = r.fields().map(|f| {
                // A field that a splice names, in a quote (macros.splices).
                let field = match f.splice() {
                    Some(s) => tagged("$", [super::exprs::opt_expr(s.value())]),
                    None => atom(f.field().map(|n| n.text()).unwrap_or_default()),
                };
                let value = match f.pattern() {
                    Some(p) => pattern(Some(p)),
                    None => field_again(&field),
                };
                list([field, value])
            });
            let rest = r.has_rest().then(|| atom(".."));
            tagged(
                "record",
                std::iter::once(r.path().map_or_else(|| atom("_"), |p| path(Some(p))))
                    .chain(fields)
                    .chain(rest),
            )
        }
        ast::Pattern::TuplePat(t) => tagged("tuple", t.patterns().map(|p| pattern(Some(p)))),
        ast::Pattern::ParenPat(p) => pattern(p.pattern()),
        ast::Pattern::ListPat(l) => {
            let rest = l.rest().map(|r| match r.name() {
                Some(n) => tagged("..", [name(Some(n))]),
                None => atom(".."),
            });
            tagged("list", l.patterns().map(|p| pattern(Some(p))).chain(rest))
        }
        ast::Pattern::OrPat(o) => tagged("or", o.patterns().map(|p| pattern(Some(p)))),
        ast::Pattern::MacroPat(m) => super::macros::macro_use(m.path(), m.group().into_iter()),
        ast::Pattern::SplicePat(s) => tagged("$", [super::exprs::opt_expr(s.value())]),
    }
}

/// A field's name written again, as the pattern of a field that binds its own name.
pub(super) fn field_again(field: &Sexp) -> Sexp {
    match field {
        Sexp::Atom(text) => atom(text.clone()),
        Sexp::List(items) => list(items.iter().map(field_again)),
    }
}

/// A pattern with the type that annotates it, in `let`, `var` or a closure.
pub(super) fn annotated(p: Option<ast::Pattern>, t: Option<ast::Type>) -> Sexp {
    match t {
        None => pattern(p),
        Some(t) => tagged(":", [pattern(p), ty(Some(t))]),
    }
}
