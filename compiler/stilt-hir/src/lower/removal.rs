//! The fix that deletes a row variable from a function's signature, wherever it is written, when
//! the type of a parameter that passes its effects through writes it (effects.row-variables and
//! effects.closure-parameters).

use stilt_diag::Edit;
use stilt_syntax::ast::{self, AstNode, Mode};
use stilt_syntax::{SyntaxKind, SyntaxNode, TextRange};

use super::{Resolver, bare};

/// Whether a parameter passes its arguments' effects through: whether its type is a function
/// type, and it is neither `inout` nor `escaping` (effects.non-escaping-parameters).
pub(super) fn passes_through(p: &ast::Param) -> bool {
    // A parameter of handler type always does (handlers.handler-types).
    !p.is_escaping()
        && p.mode() != Mode::Inout
        && p.ty()
            .is_some_and(|t| matches!(bare(&t), ast::Type::FnType(_) | ast::Type::HandlerType(_)))
}

/// Whether a row element is the row variable `name`.
fn is_var(e: &ast::RowElem, name: &str) -> bool {
    matches!(e, ast::RowElem::RowVar(v) if v.ident().is_some_and(|t| t.text() == name))
}

/// Whether a row holds the row variable `name` and nothing else, so that deleting it deletes
/// the row.
fn only(row: &ast::Row, name: &str) -> bool {
    let mut elements = row.elements().peekable();
    elements.peek().is_some() && elements.all(|e| is_var(&e, name))
}

/// Whether `node` is inside `within`, or is it.
fn inside(node: &SyntaxNode, within: Option<&SyntaxNode>) -> bool {
    within.is_some_and(|w| node.ancestors().any(|a| a == *w))
}

/// Whether a use of a row variable of the function `f` only restates what the pass-through
/// rule gives: whether it is in `f`'s own row, in its return type, or in the type of a
/// parameter that passes its effects through. Anywhere else, in another parameter's type or
/// in the body, it says something of a function that `f` keeps.
fn restates(f: &ast::Fn, var: &ast::RowVar) -> bool {
    let node = var.syntax();
    inside(node, f.row().as_ref().map(AstNode::syntax))
        || inside(node, f.ret_type().as_ref().map(AstNode::syntax))
        || f.param_list()
            .into_iter()
            .flat_map(|list| list.params())
            .any(|p| passes_through(&p) && inside(node, Some(p.syntax())))
}

/// Whether deleting the row of the function type `t` would hand it the row written after it:
/// whether the function type or function whose return type `t` is, unparenthesized, keeps a row
/// once `name` goes (declarations.function-type-rows). Of the function types in such a chain whose
/// rows go, only the outermost is parenthesized, and the rows inside it stay where they were.
fn hands_on(t: &SyntaxNode, name: &str) -> bool {
    t.parent()
        .filter(|r| r.kind() == SyntaxKind::RET_TYPE)
        .and_then(|r| r.parent())
        .and_then(|owner| owner.children().find_map(ast::Row::cast))
        .is_some_and(|row| !only(&row, name))
}

/// The edits that delete the elements marked `deleted` of a list whose elements are at
/// `spans`, of which at least one stays: each with the separator before it, or with the one
/// after it if no element that stays comes before it.
fn element_deletions(spans: &[TextRange], deleted: &[bool]) -> Vec<Edit> {
    let Some(kept) = deleted.iter().position(|d| !d) else {
        return Vec::new();
    };
    (0..spans.len())
        .filter(|&i| deleted[i])
        .map(|i| {
            if i < kept {
                Edit::delete(TextRange::new(spans[i].start(), spans[i + 1].start()))
            } else {
                Edit::delete(TextRange::new(spans[i - 1].end(), spans[i].end()))
            }
        })
        .collect()
}

impl Resolver<'_> {
    /// The edits that delete the row variable `name` from the function `f`: from its generics,
    /// and from every row that writes it. None if a use of it says something of a function that
    /// `f` keeps, which deleting it would change.
    pub(super) fn row_variable_deletion(&self, f: &ast::Fn, name: &str) -> Option<Vec<Edit>> {
        let uses: Vec<ast::RowVar> = f
            .syntax()
            .descendants()
            .filter_map(ast::RowVar::cast)
            .filter(|v| v.ident().is_some_and(|t| t.text() == name))
            .collect();
        if !uses.iter().all(|v| restates(f, v)) {
            return None;
        }
        let mut rows: Vec<ast::Row> = Vec::new();
        for row in uses
            .iter()
            .filter_map(|v| v.syntax().parent().and_then(ast::Row::cast))
        {
            if !rows.contains(&row) {
                rows.push(row);
            }
        }
        let mut edits: Vec<Edit> = rows
            .iter()
            .flat_map(|r| self.deletion_in_row(r, name))
            .collect();
        edits.extend(self.generic_deletion(f, name));
        edits.sort_by_key(|e| e.range.start());
        Some(edits)
    }

    /// The edits that delete `name` from `row`. A row left with one element loses its braces,
    /// and a row left with none goes whole. A function type whose row goes is parenthesized if
    /// the row after it would go to it instead.
    fn deletion_in_row(&self, row: &ast::Row, name: &str) -> Vec<Edit> {
        let elements: Vec<ast::RowElem> = row.elements().collect();
        let spans: Vec<TextRange> = elements.iter().map(|e| self.at(e.syntax())).collect();
        let deleted: Vec<bool> = elements.iter().map(|e| is_var(e, name)).collect();
        if only(row, name) {
            let whole = self.whole_row(row);
            let owner = row
                .syntax()
                .parent()
                .filter(|t| t.kind() == SyntaxKind::FN_TYPE);
            return match owner {
                Some(t) if hands_on(&t, name) => vec![
                    Edit::insert(self.at(&t).start(), "("),
                    Edit::replace(whole, ")"),
                ],
                _ => vec![Edit::delete(whole)],
            };
        }
        let braces: Vec<TextRange> = row
            .syntax()
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .filter(|t| matches!(t.kind(), SyntaxKind::L_CURLY | SyntaxKind::R_CURLY))
            .map(|t| self.at_token(&t))
            .collect();
        let kept: Vec<TextRange> = (0..spans.len())
            .filter(|&i| !deleted[i])
            .map(|i| spans[i])
            .collect();
        match (braces.as_slice(), kept.as_slice()) {
            ([open, close], [one]) => vec![
                Edit::delete(TextRange::new(open.start(), one.start())),
                Edit::delete(TextRange::new(one.end(), close.end())),
            ],
            _ => element_deletions(&spans, &deleted),
        }
    }

    /// The edits that delete the row variable `name` from the generics of `f`, with the whole
    /// list if it is the only one.
    fn generic_deletion(&self, f: &ast::Fn, name: &str) -> Vec<Edit> {
        let Some(list) = f.generic_list() else {
            return Vec::new();
        };
        let generics: Vec<ast::Generic> = list.generics().collect();
        let deleted: Vec<bool> = generics
            .iter()
            .map(|g| match g {
                ast::Generic::RowParam(p) => p
                    .name()
                    .and_then(|n| n.ident())
                    .is_some_and(|t| t.text() == name),
                ast::Generic::TypeParam(_) | ast::Generic::ValueParam(_) => false,
            })
            .collect();
        if !deleted.contains(&true) {
            return Vec::new();
        }
        if deleted.iter().all(|d| *d) {
            return vec![Edit::delete(self.at(list.syntax()))];
        }
        let spans: Vec<TextRange> = generics.iter().map(|g| self.at(g.syntax())).collect();
        element_deletions(&spans, &deleted)
    }
}
