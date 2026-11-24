//! Chains of field accesses, calls and indexes, such as `parts.map(f).fold(0, g)`. A chain of
//! two or more calls goes on one line when it fits, and otherwise has each call on a line of
//! its own, after a `.`, under the start of the chain; the fields that start the chain stay
//! with its first expression. A chain that doesn't fit keeps the line of its start up to the
//! arguments of its last call when that fits, and the arguments then break by themselves.

use rowan::NodeOrToken;
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::{SyntaxElement, SyntaxNode};

use super::{emit, node, significant};
use crate::stream::{Break, Builder};

/// A link of a chain: the elements that follow the expression it applies to.
struct Link {
    kind: stilt_syntax::SyntaxKind,
    elements: Vec<SyntaxElement>,
}

/// Adds a chain, from its first expression through its links.
pub(super) fn chain(n: &SyntaxNode, b: &mut Builder) {
    let mut links = Vec::new();
    let mut current = n.clone();
    while matches!(current.kind(), CALL_EXPR | FIELD_EXPR | INDEX_EXPR) {
        let mut elements = significant(&current);
        let Some(NodeOrToken::Node(receiver)) = elements.next() else {
            unreachable!("a chain link applies to an expression");
        };
        links.push(Link {
            kind: current.kind(),
            elements: elements.collect(),
        });
        current = receiver;
    }
    links.reverse();
    let calls = links.iter().filter(|l| l.kind == CALL_EXPR).count();
    let root = if calls >= 2 {
        first_call(&links)
    } else {
        links.len()
    };
    let group = (calls >= 2).then(|| b.open());
    node(&current, b);
    for (i, link) in links.iter().enumerate() {
        if i >= root && link.kind == FIELD_EXPR {
            b.brk(Break::Soft);
        }
        link.elements.iter().for_each(|e| emit(e, b));
    }
    if let Some(group) = group {
        let tail = b.tail();
        let last_is_call = links.last().is_some_and(|l| l.kind == CALL_EXPR);
        b.close_hugging(group, tail.hug.or(tail.open).filter(|_| last_is_call));
    }
}

/// The number of links at the start of a chain that stay with its first expression: the fields
/// before the last field that names the first call.
fn first_call(links: &[Link]) -> usize {
    links
        .iter()
        .position(|l| l.kind == CALL_EXPR)
        .map_or(links.len(), |call| call.saturating_sub(1))
}
