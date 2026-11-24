//! What the language server reads off a file's syntax tree alone: the spans that fold, the
//! spans around a position that a selection grows through, and the file formatted as
//! `stilt fmt` formats it, which needs no engine.

use stilt_lsp::{Fold, FoldSort};
use stilt_syntax::SyntaxKind::{self, *};
use stilt_syntax::{SyntaxNode, SyntaxToken, TextRange, TextSize};

/// The nodes whose span folds: blocks and bodies, and the bracketed lists that may run over
/// lines.
const FOLDING: [SyntaxKind; 18] = [
    BLOCK,
    RECORD_DEF,
    VARIANT_LIST,
    IMPL,
    TRAIT,
    SYNTAX,
    TEMPLATE,
    MATCH_EXPR,
    ARG_LIST,
    PARAM_LIST,
    LIST_EXPR,
    STRUCT_EXPR,
    RECORD_EXPR,
    RECORD_TYPE,
    TUPLE_EXPR,
    MACRO_GROUP,
    CATCH_CLAUSE,
    DOCS,
];

/// The spans of a file that may fold: its blocks and lists, its doc comments and runs of
/// comments, and its runs of `use` declarations. A body with a syntax error folds from its
/// brace.
#[must_use]
pub fn folds(text: &str) -> Vec<Fold> {
    let root = stilt_syntax::parse(text).syntax();
    let mut found = Vec::new();
    for node in root.descendants() {
        let kind = node.kind();
        let braced = kind == ERROR && node.first_token().is_some_and(|t| t.kind() == L_CURLY);
        if FOLDING.contains(&kind) || braced {
            let sort = if kind == DOCS {
                FoldSort::Comment
            } else {
                FoldSort::Code
            };
            found.push(fold(node.text_range(), sort));
        }
    }
    found.extend(runs(&root));
    found
}

fn fold(range: TextRange, sort: FoldSort) -> Fold {
    Fold {
        start: range.start().into(),
        end: range.end().into(),
        sort,
    }
}

/// The runs of comments, and the runs of `use` declarations, each over more than one line.
fn runs(root: &SyntaxNode) -> Vec<Fold> {
    let mut found = Vec::new();
    let mut comments: Option<TextRange> = None;
    for token in root
        .descendants_with_tokens()
        .filter_map(stilt_syntax::SyntaxElement::into_token)
    {
        match token.kind() {
            COMMENT => {
                let range = token.text_range();
                comments = Some(comments.map_or(range, |c| c.cover(range)));
            }
            WHITESPACE | NEWLINE => {}
            _ => {
                if let Some(run) = comments.take() {
                    found.push(fold(run, FoldSort::Comment));
                }
            }
        }
    }
    found.extend(comments.map(|run| fold(run, FoldSort::Comment)));
    let mut uses: Option<TextRange> = None;
    for node in root.children() {
        if node.kind() == USE {
            let range = node.text_range();
            uses = Some(uses.map_or(range, |u| u.cover(range)));
        } else if let Some(run) = uses.take() {
            found.push(fold(run, FoldSort::Imports));
        }
    }
    found.extend(uses.map(|run| fold(run, FoldSort::Imports)));
    found
}

/// The spans around `offset` of a file, from its token out to the whole file, each once.
#[must_use]
pub fn selections(text: &str, offset: u32) -> Vec<(u32, u32)> {
    let root = stilt_syntax::parse(text).syntax();
    let Some(token) = token_at(&root, TextSize::from(offset)) else {
        return Vec::new();
    };
    let mut spans: Vec<(u32, u32)> = Vec::new();
    let ranges =
        std::iter::once(token.text_range()).chain(token.parent_ancestors().map(|n| n.text_range()));
    for range in ranges {
        let span = (range.start().into(), range.end().into());
        if spans.last() != Some(&span) {
            spans.push(span);
        }
    }
    spans
}

/// The token at `offset`, preferring a word, a literal or a symbol to the trivia beside it.
#[must_use]
pub fn token_at(root: &SyntaxNode, offset: TextSize) -> Option<SyntaxToken> {
    if offset > root.text_range().end() {
        return None;
    }
    let at = root.token_at_offset(offset);
    let mut tokens: Vec<SyntaxToken> = at.collect();
    tokens.sort_by_key(|t| (t.kind().is_trivia(), !is_word(t.kind())));
    tokens.into_iter().next()
}

/// Whether a token is a word: an identifier or a keyword, contextual ones included.
#[must_use]
pub fn is_word(kind: SyntaxKind) -> bool {
    matches!(kind, LOWER_IDENT | UPPER_IDENT) || is_keyword(kind)
}

/// Whether a token is a keyword, a reserved word or a contextual keyword where it acts as one
/// (lexical.keywords, lexical.reserved-words and lexical.contextual-keywords), `meta`, `pattern`
/// and `field` among them (macros.meta-use and macros.quote).
#[must_use]
pub fn is_keyword(kind: SyntaxKind) -> bool {
    (ASSERT_KW..=FIELD_KW).contains(&kind)
}

/// `text` as `stilt fmt` formats it, or `None` when it has a syntax error or the formatter
/// would change what it means.
#[must_use]
pub fn format(text: &str) -> Option<String> {
    stilt_fmt::format(text.as_bytes()).ok()
}
