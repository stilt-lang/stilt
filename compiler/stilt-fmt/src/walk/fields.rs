//! Field punning (syntax.format.punning), interpolated strings, and statements put in parentheses.

use rowan::NodeOrToken;
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::{SyntaxElement, SyntaxNode, SyntaxToken};

use super::{children, has_token, node, significant};
use crate::space::Class;
use crate::stream::{Builder, Role};
use crate::trivia::Trivia;

/// A field of a struct literal or of a record pattern. A field whose value is a variable with
/// the field's name is written punned: `Order { customer: customer }` as `Order { customer }`,
/// in literals and patterns alike, but for the first of an anonymous record literal. A field
/// with a comment inside it is written as it is.
pub(super) fn field(n: &SyntaxNode, b: &mut Builder) {
    let elements: Vec<SyntaxElement> = significant(n).collect();
    if let [
        NodeOrToken::Node(name),
        NodeOrToken::Token(colon),
        NodeOrToken::Node(value),
    ] = elements.as_slice()
        && let Some(name) = only_token(name)
        && let Some(variable) = only_token(value)
        && matches!(
            (n.kind(), value.kind()),
            (FIELD_INIT, NAME_REF) | (FIELD_PAT, BIND_PAT)
        )
        && variable.text() == name.text()
        && !opens_record(n)
        && quiet(b, colon)
        && quiet(b, &variable)
    {
        b.token(&name);
        b.take_trivia(colon);
        b.take_trivia(&variable);
        return;
    }
    children(n, b);
}

/// Whether a field opens an anonymous record literal, which a `{` begins only when a name and a `:`
/// follow it, so that the field stays unpunned: `{ x }` is a block (records.anonymous-literals).
fn opens_record(field: &SyntaxNode) -> bool {
    field.parent().is_some_and(|p| p.kind() == RECORD_EXPR)
        && field
            .siblings(rowan::Direction::Prev)
            .skip(1)
            .all(|s| !matches!(s.kind(), FIELD_INIT | SPREAD_EXPR))
}

/// The one token of a node, if it has exactly one.
fn only_token(n: &SyntaxNode) -> Option<SyntaxToken> {
    let mut tokens = n
        .descendants_with_tokens()
        .filter_map(NodeOrToken::into_token)
        .filter(|t| !crate::trivia::is_trivia(t.kind()));
    let token = tokens.next()?;
    tokens.next().is_none().then_some(token)
}

/// Whether no comment comes before a token.
fn quiet(b: &Builder, token: &SyntaxToken) -> bool {
    b.trivia_of(token).is_none_or(|t| !t.has_comment())
}

/// An interpolated string, which stays on one line: a string can't hold a raw newline, even in its
/// interpolations (lexical.string-literals). An interpolation that holds a block, a `match` or a
/// block-form `catch` is written as it is, since the separators inside it are needed there.
pub(super) fn interpolation(n: &SyntaxNode, b: &mut Builder) {
    let breaks = n.descendants().any(|d| match d.kind() {
        BLOCK | MATCH_EXPR => true,
        CATCH_CLAUSE => has_token(&d, L_CURLY),
        _ => false,
    });
    if breaks {
        let first = n.first_token().expect("a string");
        b.verbatim(n.text().to_string(), &first, Class::Word);
    } else {
        b.flat(|b| children(n, b));
    }
}

/// A statement whose expression, or whose place, is put in parentheses.
pub(super) fn parenthesized(statement: &SyntaxNode, b: &mut Builder) {
    let first = statement.first_token().expect("a statement");
    let trivia = b.take_trivia(&first);
    let mut elements = significant(statement);
    b.synthetic("(", Class::Open, Role::Open, trivia);
    if let Some(NodeOrToken::Node(head)) = elements.next() {
        node(&head, b);
    }
    b.synthetic(")", Class::Close, Role::Close, Trivia::default());
    for element in elements {
        match element {
            NodeOrToken::Node(child) => node(&child, b),
            NodeOrToken::Token(token) => b.token(&token),
        }
    }
}
