//! The views of doc comments, and of the doc examples in them (program.doc-comments and
//! program.doc-examples).

use rowan::TextSize;

use super::{AstNode, Expr, child, tokens};
use crate::SyntaxKind::{self, *};
use crate::{SyntaxNode, SyntaxToken};

nodes! {
    /// The expression of a doc example, parsed on its own.
    Example = EXAMPLE,
    /// A run of doc comments.
    Docs = DOCS,
}

impl Example {
    /// The view of the root of a doc example's tree.
    pub(crate) fn root(node: SyntaxNode) -> Self {
        debug_assert_eq!(node.kind(), EXAMPLE);
        Self(node)
    }

    /// The example's code, parsed as an expression.
    #[must_use]
    pub fn expr(&self) -> Option<Expr> {
        child(&self.0)
    }
}

/// A line of a doc comment (program.doc-comments).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DocLine {
    /// A line of text.
    Text(String),
    /// An example, whose text is parsed as an expression, with the offset of that text in the
    /// file. The offsets in the example's tree count from it.
    Example(Example, TextSize),
    /// A property, parsed as an example is, with its text, which seeds its cases
    /// (tests.property-form and tests.seeds and tests.prop-lines and tests.draws).
    Property(Example, TextSize, String),
}

impl Docs {
    /// The doc comments.
    pub fn comments(&self) -> impl Iterator<Item = SyntaxToken> + use<> {
        tokens(&self.0).filter(|t| t.kind() == DOC_COMMENT)
    }

    /// The lines of the doc comments.
    #[must_use]
    pub fn lines(&self) -> Vec<DocLine> {
        self.comments().map(|comment| doc_line(&comment)).collect()
    }
}

/// The line of a doc comment. A line whose text, after `///` and any spaces, starts with
/// `ex:` is an example, and one that starts with `prop:` a property, whose text is the rest of
/// the line without the spaces that begin it, up to an annotation and the spaces before it
/// (tests.prop-lines). Any other line's text ends before an annotation and the spaces before it,
/// and loses one leading space.
fn doc_line(comment: &SyntaxToken) -> DocLine {
    let text = &comment.text()[3..];
    let spaces = text.bytes().take_while(|&b| b == b' ').count();
    let at = |prefix: &str| {
        let offset = TextSize::try_from(3 + spaces + prefix.len()).expect("a short prefix");
        comment.text_range().start() + offset
    };
    if let Some(example) = text[spaces..].strip_prefix("ex:") {
        return DocLine::Example(crate::parse_example(example), at("ex:"));
    }
    if let Some(property) = text[spaces..].strip_prefix("prop:") {
        let own = without_annotation(property.trim_start_matches(' ')).to_owned();
        return DocLine::Property(crate::parse_example(property), at("prop:"), own);
    }
    let text = without_annotation(text);
    DocLine::Text(text.strip_prefix(' ').unwrap_or(text).to_owned())
}

/// A doc line's text, which ends before an annotation and the spaces before it
/// (program.doc-comments).
fn without_annotation(text: &str) -> &str {
    match text.find("//~") {
        Some(i) => text[..i].trim_end_matches(' '),
        None => text,
    }
}
