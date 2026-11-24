//! How code reaches a name where it stands, for the highlights of a name in its file: it
//! writes it where it binds it, as a declaration's name, a parameter or a pattern does, where an
//! assignment changes it or a part of it (expressions.assignment), and where a call passes it
//! `inout` (expressions.inout-arguments), and it reads it everywhere else.

use stilt_lsp::{Highlight, Place};
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::{SyntaxNode, SyntaxToken, TextSize};

/// The highlights of `places`, each a span of `text`.
pub fn highlights<'p>(text: &str, places: impl IntoIterator<Item = &'p Place>) -> Vec<Highlight> {
    let root = stilt_syntax::parse(text).syntax();
    places
        .into_iter()
        .map(|p| Highlight {
            start: p.start,
            end: p.end,
            write: word_at(&root, p.start).is_some_and(|t| writes(&t)),
        })
        .collect()
}

/// The word that starts at byte `start`.
fn word_at(root: &SyntaxNode, start: u32) -> Option<SyntaxToken> {
    let at = TextSize::from(start);
    if at >= root.text_range().end() {
        return None;
    }
    root.token_at_offset(at)
        .find(|t| t.text_range().start() == at && matches!(t.kind(), LOWER_IDENT | UPPER_IDENT))
}

/// Whether code writes the name that `token` is.
fn writes(token: &SyntaxToken) -> bool {
    let Some(parent) = token.parent() else {
        return false;
    };
    if parent.kind() == NAME {
        return true;
    }
    // The place an assignment or an `inout` argument changes: the name, or the name that a
    // field or an index of it starts with.
    let mut place = parent;
    while let Some(up) = place.parent() {
        let first = up.first_child().as_ref() == Some(&place);
        match up.kind() {
            FIELD_EXPR | INDEX_EXPR if first => place = up,
            ASSIGN_STMT => return first,
            ARG => return up.children_with_tokens().any(|c| c.kind() == INOUT_KW),
            _ => return false,
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use stilt_lsp::Place;

    use super::highlights;

    fn writes(text: &str, word: &str) -> Vec<bool> {
        let places: Vec<Place> = text
            .match_indices(word)
            .filter(|(i, _)| {
                let after = text.as_bytes().get(i + word.len()).copied().unwrap_or(b' ');
                let before = if *i > 0 { text.as_bytes()[i - 1] } else { b' ' };
                !after.is_ascii_alphanumeric() && !before.is_ascii_alphanumeric()
            })
            .map(|(i, _)| Place {
                path: PathBuf::new(),
                start: u32::try_from(i).unwrap(),
                end: u32::try_from(i + word.len()).unwrap(),
            })
            .collect();
        highlights(text, &places).iter().map(|h| h.write).collect()
    }

    #[test]
    fn a_binding_and_an_assignment_write_and_the_rest_reads() {
        let text = "fn f(n: i64) -> i64 {\n  var total = n\n  total += n\n  total\n}\n";
        assert_eq!(writes(text, "total"), [true, true, false]);
        assert_eq!(writes(text, "n"), [true, false, false]);
    }

    #[test]
    fn a_change_of_a_part_or_an_inout_argument_writes_the_whole() {
        let text = "fn g(inout xs: List<i64>) {}\n\nfn f() {\n  var m = [1]\n  m[0] = 2\n  g(inout m)\n  print(\"{m}\")\n}\n";
        assert_eq!(writes(text, "m"), [true, true, true, false]);
    }
}
