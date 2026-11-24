//! What lies between two tokens of the source besides spaces: the line breaks, the blank lines and
//! the comments, which the formatter keeps (lexical.line-comments, lexical.doc-comments,
//! lexical.annotations and lexical.no-block-comments).

use rustc_hash::FxHashMap;
use stilt_syntax::SyntaxKind::{self, *};
use stilt_syntax::{SyntaxNode, SyntaxToken};

/// A line between two tokens that holds no code.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Line {
    /// One or more blank lines, which the formatter writes as one.
    Blank,
    /// A comment alone on its line.
    Comment(String),
}

/// The trivia before a token.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Trivia {
    /// Whether the source breaks the line before the token.
    pub(crate) newline: bool,
    /// A comment that ends the line of the token before.
    pub(crate) trailing: Option<String>,
    /// The lines between that line and the token's.
    pub(crate) lines: Vec<Line>,
}

impl Trivia {
    /// Whether the trivia holds a comment, which ends its line, so the line breaks there.
    pub(crate) fn has_comment(&self) -> bool {
        self.trailing.is_some() || self.lines.iter().any(|l| matches!(l, Line::Comment(_)))
    }
}

/// Whether the formatter reads a token as trivia. A `;` is one: the formatter never writes it
/// (syntax.format.separators), and writes a line break where it separates statements.
pub(crate) fn is_trivia(kind: SyntaxKind) -> bool {
    matches!(kind, WHITESPACE | NEWLINE | COMMENT | SEMICOLON)
}

/// The trivia before each token of a tree, by the token's offset, and the trivia after its
/// last token by the length of its text. Only trivia that holds something is kept: a token
/// with none has [`Trivia::default`]. A doc comment isn't trivia: each is a line that the
/// declaration after it owns (program.doc-comments).
pub(crate) fn collect(root: &SyntaxNode) -> FxHashMap<u32, Trivia> {
    let mut found = FxHashMap::default();
    let mut run: Vec<SyntaxToken> = Vec::new();
    let mut first = true;
    for token in root
        .descendants_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
    {
        if is_trivia(token.kind()) {
            run.push(token);
            continue;
        }
        let offset = u32::from(token.text_range().start());
        keep(&mut found, offset, summarize(&run, !first));
        run.clear();
        first = false;
    }
    let end = u32::from(root.text_range().end());
    keep(&mut found, end, summarize(&run, !first));
    found
}

/// Keeps `trivia` at `offset` when it holds something.
fn keep(found: &mut FxHashMap<u32, Trivia>, offset: u32, trivia: Trivia) {
    if trivia != Trivia::default() {
        found.insert(offset, trivia);
    }
}

/// The trivia that a run of trivia tokens makes, after a token on the line it starts on unless
/// the run starts the file.
fn summarize(run: &[SyntaxToken], after_token: bool) -> Trivia {
    let mut trivia = Trivia::default();
    // Whether the run is still on the line of the token before it.
    let mut first_line = after_token;
    // Whether the current line holds a comment or a `;`, which make it no blank line.
    let mut filled = false;
    for token in run {
        match token.kind() {
            NEWLINE => {
                if !first_line && !filled && trivia.lines.last() != Some(&Line::Blank) {
                    trivia.lines.push(Line::Blank);
                }
                trivia.newline = true;
                first_line = false;
                filled = false;
            }
            COMMENT if first_line => {
                trivia.trailing = Some(token.text().to_owned());
                filled = true;
            }
            COMMENT => {
                trivia.lines.push(Line::Comment(token.text().to_owned()));
                filled = true;
            }
            SEMICOLON => filled = true,
            _ => {}
        }
    }
    trivia
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The trivia before each token of `text` that isn't trivia, and after the last.
    fn trivia(text: &str) -> Vec<Trivia> {
        let root = stilt_syntax::parse(text).syntax();
        let found = collect(&root);
        root.descendants_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .filter(|t| !is_trivia(t.kind()))
            .map(|t| u32::from(t.text_range().start()))
            .chain([u32::from(root.text_range().end())])
            .map(|offset| found.get(&offset).cloned().unwrap_or_default())
            .collect()
    }

    #[test]
    fn comments_end_lines_or_fill_them() {
        let found = trivia("// top\n\nuse a // why\n\n\n// next\nuse b\n");
        assert_eq!(
            found[0].lines,
            [Line::Comment("// top".into()), Line::Blank]
        );
        assert_eq!(found[2].trailing.as_deref(), Some("// why"));
        assert_eq!(
            found[2].lines,
            [Line::Blank, Line::Comment("// next".into())]
        );
        assert!(found[2].newline);
        assert!(found[2].has_comment());
    }

    #[test]
    fn a_line_holding_a_separator_is_not_blank() {
        let found = trivia("use a\n;\nuse b");
        assert_eq!(found[2].lines, []);
        assert!(!found[2].has_comment());
    }
}
