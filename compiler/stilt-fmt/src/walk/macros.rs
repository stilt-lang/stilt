//! Macros (macros.formatting). A declaration is formatted token by token, since its patterns and
//! templates are tokens, not expressions: its arms one per line, and the separators of a
//! `{ … }` group that holds one as the statements of a block, one per line. A use's groups are
//! written as they are, but for the indentation of the lines inside them, since no macro is
//! resolved when a file is formatted, so no tool knows what forms its tokens make.

mod spacing;

use rowan::NodeOrToken;
use stilt_syntax::SyntaxKind::{self, *};
use stilt_syntax::{SyntaxNode, SyntaxToken};

use self::spacing::{Open, Prev, Shape, continues_line, ends_statement, shape, spaced};
use super::{node, significant};
use crate::stream::{Break, Builder, Role};
use crate::trivia::{Trivia, is_trivia};

/// A `syntax` declaration: its doc comments, `pub`, name and braces as an item's, and each arm
/// on a line of its own.
pub(super) fn syntax(n: &SyntaxNode, b: &mut Builder) {
    let arms: Vec<SyntaxNode> = n.children().filter(|c| c.kind() == MACRO_ARM).collect();
    let mut w = Writer { b, prev: None };
    for element in significant(n) {
        match element {
            NodeOrToken::Node(arm) if arm.kind() == MACRO_ARM => {
                w.b.brk(Break::Hard);
                w.b.element();
                w.items(&arm, &mut Open::default());
                if arms.last() != Some(&arm) && !newline_ends(&arm) {
                    w.semicolon();
                }
            }
            NodeOrToken::Node(other) => node(&other, w.b),
            NodeOrToken::Token(close) if close.kind() == R_CURLY && !arms.is_empty() => {
                w.b.brk(Break::Hard);
                w.b.token(&close);
            }
            NodeOrToken::Token(token) => w.b.token(&token),
        }
    }
}

/// Whether a newline after a node ends a statement, so that it separates the node from what
/// follows it. Where it wouldn't, a `;` does.
fn newline_ends(n: &SyntaxNode) -> bool {
    last_significant(n).is_some_and(|t| ends_statement(t.kind()))
}

fn last_significant(n: &SyntaxNode) -> Option<SyntaxToken> {
    n.descendants_with_tokens()
        .filter_map(NodeOrToken::into_token)
        .filter(|t| !is_trivia(t.kind()))
        .last()
}

/// Writes the tokens of a declaration, spacing each by the one before it.
struct Writer<'b> {
    b: &'b mut Builder,
    prev: Option<Prev>,
}

impl Writer<'_> {
    /// The elements of a node of a declaration, in order: an arm, a fragment, a repetition or
    /// a template, whose groups are laid out by themselves.
    fn items(&mut self, n: &SyntaxNode, open: &mut Open) {
        for element in significant(n) {
            match element {
                NodeOrToken::Token(token) => self.token(&token, open),
                NodeOrToken::Node(group) if group.kind() == MACRO_GROUP => self.group(&group),
                // The separator of a repetition, which is written `;`.
                NodeOrToken::Node(sep) if sep.kind() == MACRO_SEP => self.semicolon(),
                NodeOrToken::Node(other) => self.items(&other, open),
            }
        }
    }

    /// A group. A `{ … }` group laid out as a block has a line for each run of its elements
    /// between separators, a level in, and its `}` on a line of its own. In any other group, a
    /// separator is a `;`.
    fn group(&mut self, n: &SyntaxNode) {
        let block = is_block(n);
        let mut open = Open::default();
        let elements: Vec<_> = significant(n).collect();
        let last = elements.len() - 1;
        for (i, element) in elements.iter().enumerate() {
            match element {
                NodeOrToken::Token(token) => {
                    if block && i == last {
                        self.b.brk(Break::Hard);
                    }
                    self.token(token, &mut open);
                    if block && i == 0 {
                        self.b.brk(Break::Hard);
                        self.b.element();
                    }
                }
                NodeOrToken::Node(sep) if sep.kind() == MACRO_SEP => {
                    if !block || !newline_separates(sep) {
                        self.semicolon();
                    }
                    if block {
                        self.b.brk(Break::Hard);
                        self.b.element();
                    }
                }
                NodeOrToken::Node(group) if group.kind() == MACRO_GROUP => self.group(group),
                NodeOrToken::Node(other) => self.items(other, &mut open),
            }
        }
    }

    fn token(&mut self, token: &SyntaxToken, open: &mut Open) {
        let trivia = self.b.take_trivia(token);
        let shape = shape(token, self.prev, open);
        let role = match token.kind() {
            L_PAREN | L_BRACK | L_CURLY => Role::Open,
            R_PAREN | R_BRACK | R_CURLY => Role::Close,
            _ => Role::Plain,
        };
        self.write(token.text(), token.kind(), shape, role, trivia);
    }

    /// A `;` that the format writes for a separator.
    fn semicolon(&mut self) {
        self.write(";", SEMICOLON, Shape::PUNCT, Role::Plain, Trivia::default());
    }

    fn write(&mut self, text: &str, kind: SyntaxKind, shape: Shape, role: Role, trivia: Trivia) {
        let space = self.prev.is_some_and(|p| spaced(p, shape, kind, text));
        self.b.raw(text.to_owned(), space, role, trivia);
        self.prev = Some(Prev {
            kind,
            last: text.chars().last().unwrap_or(' '),
            operand: shape.operand,
            tight_after: shape.tight_after,
        });
    }
}

/// Whether a group is a `{ … }` group laid out as a block: one that holds a separator, or holds
/// such a group at any depth.
fn is_block(n: &SyntaxNode) -> bool {
    let separates = |g: &SyntaxNode| {
        g.kind() == MACRO_GROUP
            && g.first_token().is_some_and(|t| t.kind() == L_CURLY)
            && g.children().any(|c| c.kind() == MACRO_SEP)
    };
    n.first_token().is_some_and(|t| t.kind() == L_CURLY) && n.descendants().any(|d| separates(&d))
}

/// Whether the line break that a block writes for a separator separates the tokens around it
/// (lexical.terminator-insertion): the token before it ends a statement, and the one after it
/// doesn't continue the line.
fn newline_separates(sep: &SyntaxNode) -> bool {
    let Some(inner) = sep.first_token() else {
        return false;
    };
    let before = std::iter::successors(inner.prev_token(), SyntaxToken::prev_token)
        .find(|t| !is_trivia(t.kind()));
    let after = std::iter::successors(inner.next_token(), SyntaxToken::next_token)
        .find(|t| !is_trivia(t.kind()));
    before.is_some_and(|t| ends_statement(t.kind()))
        && after.is_some_and(|t| !continues_line(t.kind()))
}

/// A use, where an expression or a pattern stands: its path and `!` as written in code, and
/// each of its groups as one run of text, the trailing block a space after the group before it.
pub(super) fn macro_use(n: &SyntaxNode, b: &mut Builder) {
    for element in significant(n) {
        match element {
            NodeOrToken::Node(group) if group.kind() == MACRO_GROUP => {
                let first = group.first_token().expect("a bracket");
                let trivia = b.take_trivia(&first);
                let space = first.kind() == L_CURLY;
                b.raw(as_written(&group), space, Role::Plain, trivia);
            }
            NodeOrToken::Node(other) => node(&other, b),
            NodeOrToken::Token(bang) => {
                let trivia = b.take_trivia(&bang);
                b.raw(bang.text().to_owned(), false, Role::Plain, trivia);
            }
        }
    }
}

/// The text of a use's group as written, but for its indentation: each line inside it keeps
/// its indentation relative to the line where the group opens, which the renderer adds to the
/// indentation of the line it writes the group on. A line indented less than that one is
/// indented as much, and the spaces that end a line go.
fn as_written(group: &SyntaxNode) -> String {
    let first = group.first_token().expect("a bracket");
    let base = line_indentation(&first);
    let mut out = String::new();
    let mut pending = String::new();
    let mut line_start = false;
    for token in group
        .descendants_with_tokens()
        .filter_map(NodeOrToken::into_token)
    {
        match token.kind() {
            NEWLINE => {
                pending.clear();
                out.push('\n');
                line_start = true;
            }
            WHITESPACE if line_start => {
                pending = " ".repeat(columns(token.text()).saturating_sub(base));
                line_start = false;
            }
            WHITESPACE => token.text().clone_into(&mut pending),
            _ => {
                out.push_str(&pending);
                pending.clear();
                out.push_str(token.text());
                line_start = false;
            }
        }
    }
    out
}

/// The indentation of the source line that a token is on, in columns.
fn line_indentation(token: &SyntaxToken) -> usize {
    let mut first = token.clone();
    while let Some(prev) = first.prev_token().filter(|t| t.kind() != NEWLINE) {
        first = prev;
    }
    if first.kind() == WHITESPACE {
        columns(first.text())
    } else {
        0
    }
}

/// The columns of indentation, a tab counting as a level's two.
fn columns(text: &str) -> usize {
    text.chars().map(|c| if c == '\t' { 2 } else { 1 }).sum()
}
