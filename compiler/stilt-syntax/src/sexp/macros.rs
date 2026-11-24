//! The tree form of macros (macros.syntax-declarations and macros.uses): a declaration, with its
//! arms, and a use, its tokens unexpanded.

use super::{Sexp, atom, name, path, quote, string, tagged};
use crate::SyntaxKind::*;
use crate::SyntaxToken;
use crate::ast::{self, Bracket, MacroElem, RepOp, SeparatorKind};
use crate::text::number_text;

/// `(syntax NAME ARM…)`, where an arm is `(arm GROUP BLOCK? (template T…))`.
pub(super) fn syntax(s: &ast::Syntax) -> Sexp {
    let arms = s.arms().map(|arm| {
        let pattern = arm.pattern().map(|g| group(&g));
        let trailing = arm.trailing().map(|f| fragment(&f));
        let template = tagged(
            "template",
            arm.template()
                .into_iter()
                .flat_map(|t| t.elements())
                .map(|e| element(&e)),
        );
        tagged("arm", pattern.into_iter().chain(trailing).chain([template]))
    });
    tagged("syntax", std::iter::once(name(s.name())).chain(arms))
}

/// A token as written: a number as a string of its digits, a string literal or a piece of an
/// interpolated string as a string of its text, a format spec as a string of its spec, and a
/// separator as `;`.
pub(super) fn token(t: &SyntaxToken) -> Sexp {
    match t.kind() {
        INT | FLOAT => atom(quote(&number_text(t))),
        STRING | STRING_HEAD | STRING_MID | STRING_TAIL => string(t),
        FORMAT => atom(quote(t.text().strip_prefix(':').unwrap_or(t.text()))),
        _ => atom(t.text()),
    }
}

/// A group: `(paren T…)`, `(bracket T…)` or `(brace T…)`.
pub(super) fn group(g: &ast::MacroGroup) -> Sexp {
    let tag = match g.bracket() {
        Bracket::Paren => "paren",
        Bracket::Square => "bracket",
        Bracket::Curly => "brace",
    };
    tagged(tag, g.elements().iter().map(element))
}

/// `(frag NAME KIND)` in a pattern, and `(frag NAME)` in a template.
fn fragment(f: &ast::MacroFrag) -> Sexp {
    let text = |t: Option<SyntaxToken>| atom(t.map(|t| t.text().to_owned()).unwrap_or_default());
    match f.kind() {
        Some(kind) => tagged("frag", [text(f.name()), text(Some(kind))]),
        None => tagged("frag", [text(f.name())]),
    }
}

fn element(e: &MacroElem) -> Sexp {
    match e {
        MacroElem::Token(t) => token(t),
        MacroElem::Sep(_) => atom(";"),
        MacroElem::Group(g) => group(g),
        MacroElem::Frag(f) => fragment(f),
        MacroElem::Rep(r) => {
            let sep = match r.separator() {
                Some(SeparatorKind::Comma) => ",",
                Some(SeparatorKind::Semicolon) => ";",
                None => "_",
            };
            let op = match r.op() {
                RepOp::Star => "*",
                RepOp::Plus => "+",
            };
            tagged(
                "rep",
                [atom(sep), atom(op)].into_iter().chain(
                    r.group()
                        .into_iter()
                        .flat_map(|g| g.elements())
                        .map(|e| element(&e)),
                ),
            )
        }
    }
}

/// `(macro PATH GROUP…)`, a use with its groups unexpanded.
pub(super) fn macro_use(
    p: Option<ast::Path>,
    groups: impl Iterator<Item = ast::MacroGroup>,
) -> Sexp {
    tagged(
        "macro",
        std::iter::once(path(p)).chain(groups.map(|g| group(&g))),
    )
}
