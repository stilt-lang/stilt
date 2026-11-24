//! `without` clauses: the limits of a module header (program.header-limits) and of a function
//! (declarations.limits).

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::TextRange;
use stilt_syntax::ast::{self, AstNode, Limit};

use super::Resolver;
use crate::hir::Limits;

impl Resolver<'_> {
    /// The limits of a module header, each where it is written. A second `without` is an error
    /// at its keyword, and its limits are ignored (program.header-limits).
    pub(super) fn header_limits(&mut self, header: &ast::Header) -> Vec<(Limit, TextRange)> {
        let mut clauses = header.clauses();
        let Some(first) = clauses.next() else {
            return Vec::new();
        };
        let kept = self.clause(&first);
        for clause in clauses {
            let at = clause
                .without_token()
                .map_or_else(|| self.at(clause.syntax()), |t| self.at_token(&t));
            let d = Diagnostic::new(codes::E0202, at, "this header already has a `without`");
            let fix = self.merge(&first, &clause);
            self.diagnostics.push(d.with_fix(fix));
        }
        kept
    }

    /// The fix that names the limits of a header's later clause in its first one, and deletes
    /// the later one.
    fn merge(&self, first: &ast::Limits, later: &ast::Limits) -> Fix {
        let mut named: Vec<Limit> = first.limits().map(|(l, _)| l).collect();
        let mut added = String::new();
        for (limit, _) in later.limits() {
            if !named.contains(&limit) {
                named.push(limit);
                added.push_str(", ");
                added.push_str(limit.text());
            }
        }
        let mut edits = vec![Edit::delete(self.at(later.syntax()))];
        if !added.is_empty() {
            edits.insert(0, Edit::insert(self.at(first.syntax()).end(), added));
        }
        Fix::new("name its limits in the first `without`", edits)
    }

    /// The limits that a clause keeps, each with its span. A limit named twice is an error at its
    /// second occurrence, and is otherwise ignored (program.header-limits; declarations.limits).
    pub(super) fn clause(&mut self, clause: &ast::Limits) -> Vec<(Limit, TextRange)> {
        let named: Vec<_> = clause.limits().collect();
        let mut kept: Vec<(Limit, TextRange)> = Vec::new();
        for (i, (limit, token)) in named.iter().enumerate() {
            let at = self.at_token(token);
            if named[..i].iter().any(|(l, _)| l == limit) {
                let message = format!("`{}` is already named in this `without`", limit.text());
                // The limit goes with the `,` before it, which ends the limit before it.
                let previous = self.at_token(&named[i - 1].1).end();
                let fix = Fix::new(
                    format!("delete the repeated `{}`", limit.text()),
                    vec![Edit::delete(TextRange::new(previous, at.end()))],
                );
                let d = Diagnostic::new(codes::E0202, at, message);
                self.diagnostics.push(d.with_fix(fix));
            } else {
                kept.push((*limit, at));
            }
        }
        kept
    }
}

/// What the kept limits rule out of the implicit effects.
pub(super) fn implicit(kept: &[(Limit, TextRange)]) -> Limits {
    let has = |limit: Limit| kept.iter().any(|(l, _)| *l == limit);
    Limits {
        panic: has(Limit::Panic),
        overflow: has(Limit::Overflow),
        alloc: has(Limit::Alloc),
        div: has(Limit::Div),
        copy: has(Limit::Copy),
        locks: has(Limit::Locks),
        capabilities: kept
            .iter()
            .filter_map(|(l, _)| match l {
                Limit::Capability(c) => Some(*c),
                _ => None,
            })
            .collect(),
    }
}
