//! The constructs whose layout syntax.format.braces decides: blocks, arms and members, whose
//! entries go one per line unless a short block fits on one, the branches of an `if` with an
//! `else`, which break together, and type declarations, which go on one line when they fit and
//! otherwise put each field or variant on a line of its own.

use rowan::NodeOrToken;
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::{SyntaxElement, SyntaxNode};

use super::{emit, fields, has_token, node, significant};
use crate::stream::{Break, Builder};

/// The entries of a block, of a `match` or a block-form `catch`, or of an impl or a trait,
/// between braces. A block that holds one statement goes on one line when it fits (short
/// blocks), and so does an empty one. Every other block has one statement per line, and arms
/// always go one per line, with no comma between them, since each ends its line. A handler
/// literal of one operation is short as such a block is. An impl, a trait or an effect isn't a
/// block: its members go one per line.
pub(super) fn lines(n: &SyntaxNode, b: &mut Builder) {
    entries(n, b, false);
}

/// A branch of an `if` with an `else`, whose braces break where the group of the whole `if`
/// breaks, so that every branch of it is on one line or none is.
pub(super) fn branch(n: &SyntaxNode, b: &mut Builder) {
    entries(n, b, true);
}

fn entries(n: &SyntaxNode, b: &mut Builder, branch: bool) {
    let elements: Vec<SyntaxElement> = significant(n).collect();
    let open = elements
        .iter()
        .position(|e| e.kind() == L_CURLY)
        .expect("a `{`");
    let close = elements.len() - 1;
    if n.kind() == MATCH_EXPR {
        b.head(|b| elements[..open].iter().for_each(|e| emit(e, b)));
    } else {
        elements[..open].iter().for_each(|e| emit(e, b));
    }
    let entries = elements[open + 1..close]
        .iter()
        .filter(|e| e.as_node().is_some())
        .count();
    let (brk, grouped) = match (n.kind(), entries) {
        // A handler literal of one operation is short as a block of one statement is, as the
        // guide writes it (handlers.handler-literals).
        (_, 0) | (BLOCK | HANDLER_EXPR, 1) => (Break::Soft, !branch),
        _ => (Break::Hard, false),
    };
    let group = grouped.then(|| b.open());
    if n.parent().is_some_and(|p| p.kind() == CLOSURE_EXPR) {
        b.closure_block();
    }
    let brace = elements[open].as_token().expect("a `{`");
    if after_fallback(n) {
        b.token(brace);
    } else {
        b.body_open(brace);
    }
    let mut first = true;
    for (i, element) in elements.iter().enumerate().take(close).skip(open + 1) {
        match element {
            NodeOrToken::Node(entry) => {
                b.brk(brk);
                b.element();
                if !first && n.kind() == BLOCK && continues_line(entry) {
                    fields::parenthesized(entry, b);
                } else {
                    node(entry, b);
                }
                first = false;
            }
            NodeOrToken::Token(comma) if matches!(n.kind(), MATCH_EXPR | CATCH_CLAUSE) => {
                b.skip(comma);
            }
            NodeOrToken::Token(comma) if i + 1 == close => b.trailing_comma(comma),
            NodeOrToken::Token(token) => b.token(token),
        }
    }
    b.brk(brk);
    b.token(elements[close].as_token().expect("a `}`"));
    if let Some(group) = group {
        b.close(group);
    }
}

/// Whether the braces are those of a block-form `catch`, or of a block after `else` or after a
/// one-arm `catch`, which open on the line where the expression before them ends, and whose
/// entries go one level deeper than that line, as inside a bracket.
fn after_fallback(n: &SyntaxNode) -> bool {
    let parent = n.parent();
    let last = |p: &SyntaxNode| p.last_child().is_some_and(|c| &c == n);
    match n.kind() {
        CATCH_CLAUSE => true,
        BLOCK => parent.is_some_and(|p| match p.kind() {
            ELSE_EXPR => last(&p),
            ARM => {
                last(&p)
                    && p.parent()
                        .is_some_and(|c| c.kind() == CATCH_CLAUSE && !has_token(&c, L_CURLY))
            }
            _ => false,
        }),
        _ => false,
    }
}

/// Whether a statement starts with a token that continues the line before it
/// (lexical.continuation-lines and lexical.terminator-insertion), which only a `;` could separate
/// from the statement before. The formatter writes no `;`, so it puts such a statement in
/// parentheses, which leave no trace in its tree.
fn continues_line(statement: &SyntaxNode) -> bool {
    statement
        .first_token()
        .is_some_and(|t| matches!(t.kind(), DOT | PIPE))
}

/// The fields of a record type, on one line when the declaration fits in 100 columns, and
/// otherwise each on a line of its own, followed by a comma, the last too.
pub(super) fn record(n: &SyntaxNode, b: &mut Builder) {
    let elements: Vec<SyntaxElement> = significant(n).collect();
    let close = elements.len() - 1;
    let group = b.open();
    b.token(elements[0].as_token().expect("a `{`"));
    for (i, element) in elements.iter().enumerate().take(close).skip(1) {
        match element {
            NodeOrToken::Node(field) => {
                b.brk(Break::Soft);
                b.element();
                b.flat(|b| node(field, b));
            }
            NodeOrToken::Token(comma) if i + 1 == close => b.trailing_comma(comma),
            NodeOrToken::Token(token) => b.token(token),
        }
    }
    if elements[close - 1].as_node().is_some() {
        b.synthetic_trailing_comma();
    }
    b.brk(Break::Soft);
    b.token(elements[close].as_token().expect("a `}`"));
    b.close(group);
}

/// The variants of a variant type, on one line when the declaration fits in 100 columns, and
/// otherwise each on a line of its own, which starts with the `|` before it.
pub(super) fn variants(n: &SyntaxNode, b: &mut Builder) {
    let group = b.open_owning();
    for (i, element) in significant(n).enumerate() {
        match element {
            NodeOrToken::Token(bar) => {
                b.brk(Break::Soft);
                b.token(&bar);
            }
            NodeOrToken::Node(variant) => {
                if i == 0 {
                    b.brk(Break::Soft);
                }
                b.flat(|b| node(&variant, b));
            }
        }
    }
    b.close(group);
}
