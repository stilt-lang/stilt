//! A template with its fragments substituted (macros.templates and macros.matching): by the forms a
//! use's tokens matched, each in parentheses when it is an expression, a pattern or a type, so that
//! it stays one form, and, when a declaration is checked, by a placeholder of its kind
//! (macros.checked-templates).

use std::collections::HashMap;

use stilt_syntax::{SyntaxKind, TextRange};

use super::{FragKind, TItem, bracket_text};
use crate::hir::Name;

/// A token of a use or of an expansion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Tok {
    pub(crate) kind: SyntaxKind,
    pub(crate) text: Name,
    /// Where it is reported: where the user wrote it, or the use whose template wrote it.
    pub(crate) at: TextRange,
    /// Whether the user wrote it, as a fragment's tokens.
    pub(crate) user: bool,
    /// The expansion whose template wrote it, or 0 for the user's code (macros.hygiene).
    pub(crate) mark: u32,
}

/// What a fragment matched: the tokens of one form, or one binding for each match of the
/// repetition it is in.
#[derive(Clone, Debug)]
pub(crate) enum Bound {
    One(Vec<Tok>),
    Many(Vec<Bound>),
}

/// The fragments an arm's pattern bound, each with its kind.
pub(crate) type Bindings = HashMap<Name, (FragKind, Bound)>;

/// Makes a token the template itself writes: its kind, its text, and where the template has it.
pub(crate) type Own<'a> = dyn Fn(SyntaxKind, &Name, TextRange) -> Tok + 'a;

/// The tokens of a fragment in an expansion, written at `at` in the template: in parentheses
/// when it stays one form by them, which are the template's own tokens.
fn fragment(kind: FragKind, tokens: &[Tok], (own, at): (&Own<'_>, TextRange), out: &mut Vec<Tok>) {
    if !kind.parenthesized() {
        out.extend_from_slice(tokens);
        return;
    }
    out.push(own(SyntaxKind::L_PAREN, &Name::from("("), at));
    out.extend_from_slice(tokens);
    out.push(own(SyntaxKind::R_PAREN, &Name::from(")"), at));
}

/// A template with its fragments' bindings, and each of its own tokens made by `own`.
pub(crate) struct Expander<'a> {
    pub(crate) bindings: &'a Bindings,
    pub(crate) own: &'a Own<'a>,
}

impl Expander<'_> {
    /// The tokens of `items`, inside the matches of repetitions `path` gives.
    pub(crate) fn items(&self, items: &[TItem], path: &mut Vec<usize>, out: &mut Vec<Tok>) {
        for item in items {
            match item {
                TItem::Token(kind, text, at) => out.push((self.own)(*kind, text, *at)),
                TItem::Group(bracket, inner, open, close) => {
                    let (kind, text) = bracket_text(*bracket, true);
                    out.push((self.own)(kind, &Name::from(text), *open));
                    self.items(inner, path, out);
                    let (kind, text) = bracket_text(*bracket, false);
                    out.push((self.own)(kind, &Name::from(text), *close));
                }
                TItem::Frag(name, at) => {
                    if let Some((kind, bound)) = self.bindings.get(name)
                        && let Bound::One(tokens) = descend(bound, path)
                    {
                        fragment(*kind, tokens, (self.own, *at), out);
                    }
                }
                TItem::Rep(rep) => {
                    for i in 0..length(self, &rep.items, path).unwrap_or(0) {
                        if i > 0
                            && let Some(sep) = rep.sep
                        {
                            let text = if sep == SyntaxKind::COMMA { "," } else { ";" };
                            out.push((self.own)(sep, &Name::from(text), rep.at));
                        }
                        path.push(i);
                        self.items(&rep.items, path, out);
                        path.pop();
                    }
                }
            }
        }
    }
}

/// How many times a repetition of the template repeats: the number of matches of the
/// repetition of the pattern that its fragments come from, at the level `path` gives, whether
/// they are in it or in a repetition nested in it.
fn length(e: &Expander<'_>, items: &[TItem], path: &[usize]) -> Option<usize> {
    items.iter().find_map(|item| match item {
        TItem::Frag(name, _) => match e.bindings.get(name) {
            Some((_, bound)) => match descend(bound, path) {
                Bound::Many(all) => Some(all.len()),
                Bound::One(_) => None,
            },
            None => None,
        },
        TItem::Rep(rep) => length(e, &rep.items, path),
        TItem::Group(_, inner, ..) => length(e, inner, path),
        TItem::Token(..) => None,
    })
}

/// The binding inside the matches that `path` gives.
fn descend<'b>(bound: &'b Bound, path: &[usize]) -> &'b Bound {
    path.iter().fold(bound, |b, &i| match b {
        Bound::Many(all) => all.get(i).unwrap_or(b),
        Bound::One(_) => b,
    })
}

/// A template's tokens with each fragment a placeholder of its kind, where the fragment is
/// written, and each repetition written once, as a declaration's check parses and resolves it
/// (macros.checked-templates). The template's own tokens are made by `own`. A placeholder stands
/// alone, one form of its kind, without the parentheses an expansion writes around a fragment
/// (macros.expansion), so that `100 $body` is two expressions, and E0221, rather than a call of
/// `100`.
pub(crate) fn placeholders(
    items: &[TItem],
    kinds: &HashMap<Name, FragKind>,
    own: &Own<'_>,
) -> Vec<Tok> {
    let mut out = Vec::new();
    write_placeholders(items, kinds, own, &mut out);
    out
}

fn write_placeholders(
    items: &[TItem],
    kinds: &HashMap<Name, FragKind>,
    own: &Own<'_>,
    out: &mut Vec<Tok>,
) {
    for item in items {
        match item {
            TItem::Token(kind, text, at) => out.push(own(*kind, text, *at)),
            TItem::Group(bracket, inner, open, close) => {
                let (kind, text) = bracket_text(*bracket, true);
                out.push(own(kind, &Name::from(text), *open));
                write_placeholders(inner, kinds, own, out);
                let (kind, text) = bracket_text(*bracket, false);
                out.push(own(kind, &Name::from(text), *close));
            }
            TItem::Frag(name, at) => {
                let kind = kinds.get(name).copied().unwrap_or(FragKind::Expr);
                out.extend(placeholder(kind).iter().map(|&(kind, text)| Tok {
                    kind,
                    text: Name::from(text),
                    at: *at,
                    user: true,
                    mark: 0,
                }));
            }
            TItem::Rep(rep) => write_placeholders(&rep.items, kinds, own, out),
        }
    }
}

/// A form of each kind, which stands for a fragment of that kind.
pub(crate) fn placeholder(kind: FragKind) -> &'static [(SyntaxKind, &'static str)] {
    use SyntaxKind::{L_CURLY, LOWER_IDENT, QUESTION, R_CURLY, UNDERSCORE, UPPER_IDENT};
    match kind {
        FragKind::Expr => &[(QUESTION, "?")],
        FragKind::Pattern => &[(UNDERSCORE, "_")],
        FragKind::Type => &[(UPPER_IDENT, "T")],
        FragKind::Block => &[(L_CURLY, "{"), (R_CURLY, "}")],
        FragKind::Lower => &[(LOWER_IDENT, "x")],
        FragKind::Upper => &[(UPPER_IDENT, "X")],
    }
}
