//! Parameters that pass their arguments' effects through, whose types write no row variable
//! (effects.rows and effects.non-escaping-parameters).

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::ast::{self, AstNode};

use super::Resolver;
use super::removal::passes_through;

/// The effects that are written as row variables nowhere, which E0501 reports instead.
const IMPLICIT_EFFECTS: [&str; 2] = ["panic", "alloc"];

impl Resolver<'_> {
    /// effects.row-variables: a row variable written in the type of a non-escaping parameter, at
    /// any depth, is an error at the first one in source order, and the parameter's type is then
    /// the error type. Tells whether the parameter `p` has one.
    ///
    /// The first fix deletes the variable from the whole signature, when every other use of it
    /// is one that the pass-through rule makes redundant too. The second marks the parameter
    /// `escaping`.
    pub(super) fn row_variable_on_passing(&mut self, p: &ast::Param) -> bool {
        if !passes_through(p) {
            return false;
        }
        let Some((var, name)) = p
            .syntax()
            .descendants()
            .filter_map(ast::RowVar::cast)
            .filter_map(|v| v.ident().map(|t| (v, t)))
            .find(|(_, t)| !IMPLICIT_EFFECTS.contains(&t.text()))
        else {
            return false;
        };
        let at = self.at(var.syntax());
        let param = p.name().and_then(|n| n.ident());
        let shown = param.as_ref().map_or("this parameter", |t| t.text());
        let message =
            format!("`{shown}` passes its effects through, so its type names no row variable");
        let mut d = Diagnostic::new(codes::E0509, at, message)
            .with_label("its effects pass through without it");
        let deletion = p
            .syntax()
            .ancestors()
            .find_map(ast::Fn::cast)
            .and_then(|f| self.row_variable_deletion(&f, name.text()));
        if let Some(edits) = deletion {
            let title = format!("delete `{}` from the signature", name.text());
            d = d.with_fix(Fix::new(title, edits));
        }
        if let Some(param) = param {
            let start = self.at_token(&param).start();
            let title = format!(
                "mark `{}` `escaping`, if the function keeps it",
                param.text()
            );
            d = d.with_fix(Fix::new(title, vec![Edit::insert(start, "escaping ")]));
        }
        self.diagnostics.push(d);
        true
    }
}
