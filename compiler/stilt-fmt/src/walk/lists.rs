//! Lists in brackets: arguments, parameters, payloads, elements, tuples, record literals and
//! patterns. A list goes on one line when it fits, and otherwise has one element per line, a
//! comma after each (the last included, unless it is a `..`), and its closing bracket on a line
//! of its own. A list of literals fills its lines instead. A list whose last argument is a
//! closure with a block stays on the line of its start when that fits, as in
//! `items.for_each(|item| {`.

use rowan::NodeOrToken;
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::{SyntaxElement, SyntaxNode};

use super::{emit, node, significant};
use crate::stream::{Break, Builder, Tail};

/// Adds a list: what comes before its opening bracket, the bracket, the elements, and the
/// closing bracket. Returns the group of the list, unless it has none, since it never breaks.
pub(super) fn list(n: &SyntaxNode, b: &mut Builder) -> Option<usize> {
    let elements: Vec<SyntaxElement> = significant(n).collect();
    let open = elements
        .iter()
        .position(|e| matches!(e.kind(), L_PAREN | L_BRACK | L_CURLY))
        .expect("an opening bracket");
    let close = elements.len() - 1;
    elements[..open].iter().for_each(|e| emit(e, b));
    let count = elements[open + 1..close]
        .iter()
        .filter(|e| e.as_node().is_some())
        .count();
    let plain = count == 0 || sole_string(&elements[open + 1..close]);
    let group = (!plain).then(|| b.open());
    let open_at = b.len();
    emit(&elements[open], b);
    b.element();
    let rest_last = elements[open + 1..close]
        .iter()
        .rev()
        .find_map(|e| e.as_node())
        .is_some_and(|last| last.kind() == REST_PAT);
    let gap = if plain {
        Break::Flat
    } else if fills(n) {
        Break::Fill
    } else {
        Break::Soft
    };
    let hug = entries(n, &elements[open + 1..close], gap, rest_last, b);
    let ended_with_comma = elements[open + 1..close]
        .last()
        .is_some_and(|e| e.kind() == COMMA);
    if plain {
        emit(&elements[close], b);
        b.set_tail(Tail::default());
        return None;
    }
    if !ended_with_comma && !rest_last {
        b.synthetic_trailing_comma();
    }
    b.brk(Break::Soft);
    emit(&elements[close], b);
    if let Some(group) = group {
        b.close_hugging(group, hug);
    }
    b.set_tail(Tail {
        open: Some(open_at),
        hug,
    });
    group
}

/// Adds the elements of a list between its brackets, each after a gap that breaks as `gap`
/// says, but the first, after which a list that fills its lines breaks as any other, and
/// returns the `{` of the closure's block that ends it, if one does.
fn entries(
    list: &SyntaxNode,
    elements: &[SyntaxElement],
    gap: Break,
    rest_last: bool,
    b: &mut Builder,
) -> Option<usize> {
    let mut hug = None;
    let mut first = true;
    for (i, element) in elements.iter().enumerate() {
        match element {
            NodeOrToken::Node(entry) => {
                b.brk(if first && gap == Break::Fill {
                    Break::Soft
                } else {
                    gap
                });
                first = false;
                b.element();
                let start = b.len();
                node(entry, b);
                hug = closes_with_block(list, entry)
                    .then(|| b.closure_block_since(start))
                    .flatten();
            }
            NodeOrToken::Token(comma) => {
                let at_end = i + 1 == elements.len();
                if at_end && rest_last {
                    b.drop(comma);
                } else if at_end && !one_tuple(list) {
                    b.trailing_comma(comma);
                } else {
                    b.token(comma);
                    b.element();
                }
            }
        }
    }
    hug
}

/// Whether the elements of a list are one string, which breaking the list wouldn't shorten.
fn sole_string(elements: &[SyntaxElement]) -> bool {
    let mut nodes = elements.iter().filter_map(|e| e.as_node());
    let (Some(only), None) = (nodes.next(), nodes.next()) else {
        return false;
    };
    let value = if only.kind() == ARG {
        only.children().next()
    } else {
        Some(only.clone())
    };
    value.is_some_and(|v| {
        matches!(v.kind(), LITERAL | INTERP) && v.text().to_string().starts_with('"')
    })
}

/// Whether a list fills its lines (syntax.format.literal-lists): it is a list literal whose
/// elements are all literals, a literal being a number, possibly negated, a string or a boolean,
/// and which holds no comment.
fn fills(n: &SyntaxNode) -> bool {
    let literal = |e: &SyntaxNode| match e.kind() {
        LITERAL | INTERP => true,
        PREFIX_EXPR => {
            e.first_token().is_some_and(|t| t.kind() == MINUS)
                && e.children().next().is_some_and(|operand| {
                    operand.kind() == LITERAL
                        && operand
                            .first_token()
                            .is_some_and(|t| matches!(t.kind(), INT | FLOAT))
                })
        }
        _ => false,
    };
    n.kind() == LIST_EXPR
        && n.children().all(|e| literal(&e))
        && !n
            .descendants_with_tokens()
            .skip_while(|e| e.kind() != L_BRACK)
            .any(|e| e.kind() == COMMENT)
}

/// Whether a tuple holds one element, whose comma tells it from parentheses that group.
fn one_tuple(n: &SyntaxNode) -> bool {
    matches!(n.kind(), TUPLE_EXPR | TUPLE_TYPE | TUPLE_PAT)
        && significant(n).filter(|e| e.as_node().is_some()).count() == 1
}

/// Whether an argument is the last of a list of arguments and is a closure whose body is a
/// block.
fn closes_with_block(list: &SyntaxNode, entry: &SyntaxNode) -> bool {
    list.kind() == ARG_LIST
        && significant(list)
            .filter_map(NodeOrToken::into_node)
            .last()
            .is_some_and(|last| &last == entry)
        && entry
            .children()
            .find(|c| c.kind() == CLOSURE_EXPR)
            .is_some_and(|closure| closure.last_child().is_some_and(|c| c.kind() == BLOCK))
}
