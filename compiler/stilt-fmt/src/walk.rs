//! The walk of a tree that builds the stream of its tokens: the gaps that the canonical format
//! decides (syntax.format), and the groups that go on one line when they fit. Every gap that
//! isn't a break of a group stays on its line.

mod braces;
mod chain;
mod fields;
mod lists;
mod macros;
mod ops;

use rowan::NodeOrToken;
use stilt_syntax::SyntaxKind::{self, *};
use stilt_syntax::{SyntaxElement, SyntaxNode};

use crate::stream::{Break, Builder};
use crate::trivia::is_trivia;

/// Adds the tokens of a file: its header and items, each on a line of its own.
pub(crate) fn file(root: &SyntaxNode, b: &mut Builder) {
    for (i, child) in root.children().enumerate() {
        if i > 0 {
            b.brk(Break::Hard);
        }
        b.element();
        node(&child, b);
    }
}

/// Adds the tokens of a node.
fn node(n: &SyntaxNode, b: &mut Builder) {
    match n.kind() {
        HEADER => header(n, b),
        DOCS => docs(n, b),
        LIMITS => limits(n, b),
        BLOCK | MATCH_EXPR | IMPL | TRAIT | EFFECT | HANDLER_EXPR => braces::lines(n, b),
        CATCH_CLAUSE if has_token(n, L_CURLY) => braces::lines(n, b),
        RECORD_DEF => braces::record(n, b),
        VARIANT_LIST => braces::variants(n, b),
        FIELD_INIT | FIELD_PAT => fields::field(n, b),
        ARG_LIST | PARAM_LIST | PAYLOAD_LIST | PARAM_TYPE_LIST | LIST_EXPR | TUPLE_EXPR
        | TUPLE_TYPE | TUPLE_PAT | LIST_PAT | VARIANT_PAT | STRUCT_EXPR | RECORD_PAT => {
            lists::list(n, b);
        }
        FN | FN_TYPE | OPERATION => signature(n, b),
        BINARY_EXPR | ELSE_EXPR => ops::operators(n, b),
        OR_PAT => ops::alternatives(n, b),
        TRY_EXPR => ops::try_expr(n, b),
        CALL_EXPR | FIELD_EXPR | INDEX_EXPR => chain::chain(n, b),
        IF_EXPR | WHILE_EXPR | FOR_EXPR => ops::control(n, b),
        INTERP => fields::interpolation(n, b),
        SYNTAX => macros::syntax(n, b),
        MACRO_USE | MACRO_PAT | MACRO_TYPE => macros::macro_use(n, b),
        _ => children(n, b),
    }
}

/// Adds the children of a node in order, each on the line of the one before.
///
/// In a list in brackets, each element starts at its first token.
fn children(n: &SyntaxNode, b: &mut Builder) {
    let bracketed = n
        .children_with_tokens()
        .any(|e| matches!(e.kind(), L_PAREN | L_BRACK | L_CURLY));
    for element in significant(n) {
        match element {
            NodeOrToken::Node(child) => node(&child, b),
            NodeOrToken::Token(token) => {
                b.token(&token);
                if matches!(token.kind(), L_PAREN | L_BRACK | L_CURLY)
                    || (bracketed && token.kind() == COMMA)
                {
                    b.element();
                }
            }
        }
    }
}

/// Adds a child of a node.
fn emit(element: &SyntaxElement, b: &mut Builder) {
    match element {
        NodeOrToken::Node(child) => node(child, b),
        NodeOrToken::Token(token) => b.token(token),
    }
}

/// The children of a node that the formatter writes: its nodes, and its tokens but trivia.
fn significant(n: &SyntaxNode) -> impl Iterator<Item = SyntaxElement> + use<> {
    n.children_with_tokens().filter(|e| !is_trivia(e.kind()))
}

/// Whether a node has a token of a kind among its children.
fn has_token(n: &SyntaxNode, kind: SyntaxKind) -> bool {
    n.children_with_tokens().any(|e| e.kind() == kind)
}

/// A function or a function type, whose parameter list breaks before its return type, its row
/// and its `where` clause do: they are tied to the list, which goes on one line only when they fit
/// on it too (syntax.format.signatures). A function's `without` clause breaks first: the signature
/// is a group that ends with the clause, which goes on the next line, a level in, when the whole
/// signature doesn't fit on one line (lexical.terminator-insertion).
fn signature(n: &SyntaxNode, b: &mut Builder) {
    let mut whole = n.children().any(|c| c.kind() == LIMITS).then(|| b.open());
    let mut params = None;
    for element in significant(n) {
        if matches!(element.kind(), BLOCK | HOLE_BODY | LIMITS)
            && let Some(group) = params.take()
        {
            b.tie(group);
        }
        match &element {
            NodeOrToken::Node(list) if matches!(list.kind(), PARAM_LIST | PARAM_TYPE_LIST) => {
                params = lists::list(list, b);
            }
            NodeOrToken::Node(limits) if limits.kind() == LIMITS => {
                b.brk(Break::Soft);
                node(limits, b);
                if let Some(group) = whole.take() {
                    b.close(group);
                }
            }
            _ => emit(&element, b),
        }
    }
    if let Some(group) = params {
        b.tie(group);
    }
}

/// The module header, and each of its `without` clauses on a line of its own
/// (program.module-header).
fn header(n: &SyntaxNode, b: &mut Builder) {
    for element in significant(n) {
        match element {
            NodeOrToken::Node(child) if child.kind() == LIMITS => {
                b.brk(Break::Hard);
                b.element();
                node(&child, b);
            }
            NodeOrToken::Node(child) => node(&child, b),
            NodeOrToken::Token(token) => b.token(&token),
        }
    }
}

/// The limits of a `without` clause, which go on one line when they fit and otherwise one per
/// line, the first with the `without`.
fn limits(n: &SyntaxNode, b: &mut Builder) {
    let group = b.open();
    let mut after_comma = false;
    for element in significant(n) {
        if after_comma {
            b.brk(Break::Soft);
        }
        after_comma = element.kind() == COMMA;
        emit(&element, b);
    }
    b.close(group);
}

/// The doc comments of a declaration, each on a line of its own, and the declaration on the
/// line after them (program.doc-comments).
fn docs(n: &SyntaxNode, b: &mut Builder) {
    let comments = n
        .children_with_tokens()
        .filter_map(NodeOrToken::into_token)
        .filter(|t| t.kind() == DOC_COMMENT);
    for (i, comment) in comments.enumerate() {
        if i > 0 {
            b.brk(Break::Hard);
            b.element();
        }
        b.token(&comment);
    }
    b.brk(Break::Hard);
    b.element();
}
