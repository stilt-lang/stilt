//! The check that formatting keeps what a file means: the formatted text parses, to the tree
//! form of the source's (syntax.tree-form), and holds the same comments, in the
//! same order.

use stilt_syntax::SyntaxKind::*;
use stilt_syntax::{Parse, SyntaxNode, sexp};

pub(crate) fn same(source: &Parse, formatted: &str) -> bool {
    let reparsed = stilt_syntax::parse(formatted);
    reparsed.error().is_none()
        && sexp::module(&source.tree()) == sexp::module(&reparsed.tree())
        && comments(&source.syntax()) == comments(&reparsed.syntax())
}

fn comments(root: &SyntaxNode) -> Vec<String> {
    root.descendants_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| matches!(t.kind(), COMMENT | DOC_COMMENT))
        .map(|t| t.text().to_owned())
        .collect()
}
