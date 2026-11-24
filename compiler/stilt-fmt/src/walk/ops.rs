//! Expressions and patterns that break after an operator or before a keyword when they don't
//! fit: binary operators, `else`, `|` in patterns, `catch`, and the heads of control constructs.

use rowan::NodeOrToken;
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::{SyntaxElement, SyntaxNode, SyntaxToken};

use super::{braces, emit, has_token, node, significant};
use crate::stream::{Break, Builder};

/// A binary expression, or an expression with `else`. Operands of the same operator, as in
/// `a + b + c`, are one group, which breaks after each operator, or before each `else` but one
/// whose fallback is a block, which opens on the line where the expression ends: the group then
/// keeps its line up to the block's brace when that fits, as a call does before a closure's
/// block. `>` and `>>` don't break, since they could close a generic type and so end the line
/// (lexical.continuing-expression).
pub(super) fn operators(n: &SyntaxNode, b: &mut Builder) {
    operands(n, b);
}

/// Adds the group of a binary expression or an expression with `else`, and returns the brace
/// of the block that ends it, if a block after `else` does. `else` groups to the right, so a
/// chain of them nests, each group keeping its line up to that brace.
fn operands(n: &SyntaxNode, b: &mut Builder) -> Option<usize> {
    let mut rest: Vec<(SyntaxToken, SyntaxNode)> = Vec::new();
    let mut current = n.clone();
    let head = loop {
        let parts: Vec<SyntaxElement> = significant(&current).collect();
        let [
            NodeOrToken::Node(left),
            NodeOrToken::Token(op),
            NodeOrToken::Node(right),
        ] = parts.as_slice()
        else {
            unreachable!("an operator between two operands");
        };
        rest.push((op.clone(), right.clone()));
        if left.kind() == n.kind() && operator(left).is_some_and(|l| l.kind() == op.kind()) {
            current = left.clone();
        } else {
            break left.clone();
        }
    };
    let group = b.open();
    node(&head, b);
    let mut hug = None;
    for (op, right) in rest.iter().rev() {
        hug = None;
        match op.kind() {
            ELSE_KW if right.kind() == BLOCK => {
                b.token(op);
                hug = Some(b.len());
            }
            ELSE_KW => {
                b.brk(Break::Soft);
                b.token(op);
            }
            R_ANGLE | SHR => b.token(op),
            _ => {
                b.token(op);
                b.brk(Break::Soft);
            }
        }
        if op.kind() == ELSE_KW && right.kind() == ELSE_EXPR {
            hug = operands(right, b);
        } else {
            node(right, b);
        }
    }
    b.close_hugging(group, hug);
    hug
}

/// The operator of a binary expression.
fn operator(n: &SyntaxNode) -> Option<SyntaxToken> {
    significant(n).find_map(NodeOrToken::into_token)
}

/// A pattern of alternatives, which breaks before each `|` when it doesn't fit.
pub(super) fn alternatives(n: &SyntaxNode, b: &mut Builder) {
    let group = b.open();
    for element in significant(n) {
        if element.kind() == PIPE {
            b.brk(Break::Soft);
        }
        emit(&element, b);
    }
    b.close(group);
}

/// A `try`, whose `catch` in the form of one arm goes on a line of its own when the whole
/// doesn't fit, unless the arm's body is a block. A block, or the block form, opens its braces
/// on the line where the expression ends, after the `catch`.
pub(super) fn try_expr(n: &SyntaxNode, b: &mut Builder) {
    let group = b.open();
    for element in significant(n) {
        if let NodeOrToken::Node(clause) = &element
            && clause.kind() == CATCH_CLAUSE
            && !has_token(clause, L_CURLY)
            && clause
                .children()
                .find(|c| c.kind() == ARM)
                .and_then(|arm| arm.last_child())
                .is_none_or(|body| body.kind() != BLOCK)
        {
            b.brk(Break::Soft);
        }
        emit(&element, b);
    }
    b.close(group);
}

/// An `if`, a `while` or a `for`, whose head goes two levels in where it continues, so that its
/// body doesn't look like a part of it. An `if` with an `else` is one group, which goes on one
/// line when it fits and otherwise breaks the braces of every branch.
pub(super) fn control(n: &SyntaxNode, b: &mut Builder) {
    if n.kind() == IF_EXPR && has_token(n, ELSE_KW) {
        let group = b.open();
        branches(n, b);
        b.close(group);
    } else {
        for element in &head(n, b) {
            emit(element, b);
        }
    }
}

/// The head and the branches of an `if` in a chain of `else if`, each branch a block whose
/// braces break with the chain.
fn branches(n: &SyntaxNode, b: &mut Builder) {
    for element in &head(n, b) {
        match element {
            NodeOrToken::Node(block) if block.kind() == BLOCK => braces::branch(block, b),
            NodeOrToken::Node(next) if next.kind() == IF_EXPR => branches(next, b),
            _ => emit(element, b),
        }
    }
}

/// Adds the head of a control construct, and returns the rest: its body, and the `else` of an
/// `if` with its branch.
fn head(n: &SyntaxNode, b: &mut Builder) -> Vec<SyntaxElement> {
    let mut elements: Vec<SyntaxElement> = significant(n).collect();
    let body = elements
        .iter()
        .position(|e| e.kind() == BLOCK)
        .unwrap_or(elements.len());
    let rest = elements.split_off(body);
    b.head(|b| elements.iter().for_each(|e| emit(e, b)));
    rest
}
