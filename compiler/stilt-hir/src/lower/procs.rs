//! Procedural macros' declarations (macros.procedural-declarations): a function of its signature,
//! whose parameters take `std.meta`'s input types, only the last `meta.Tokens`, whose result is
//! `meta.Expr`, `meta.Pattern` or `meta.Type`, which may raise only `meta.Error`, and which has no
//! generics and no `without` clause. Anything else is E0228, at the part that breaks the rule.

use stilt_diag::codes;
use stilt_syntax::TextRange;
use stilt_syntax::ast::{self, AstNode};

use super::Resolver;
use super::decls::recovered;
use crate::hir::{FnDecl, Input, Param, Ty, is_meta_error, result_form};

impl Resolver<'_> {
    /// Reports each part of a macro's declaration that breaks macros.procedural-declarations. A
    /// type with an error breaks none (errors.error-type).
    pub(super) fn check_macro(&mut self, f: &ast::Fn, decl: &FnDecl) {
        if recovered(f.syntax()) {
            return;
        }
        if let Some(g) = f.generic_list().and_then(|l| l.generics().next()) {
            let at = g
                .name()
                .map_or_else(|| self.at(g.syntax()), |n| self.at(n.syntax()));
            self.malformed(at, "has no generics");
        }
        if let Some(clause) = f.limits() {
            let at = clause
                .without_token()
                .map_or_else(|| self.at(clause.syntax()), |t| self.at_token(&t));
            self.malformed(at, "has no `without` clause");
        }
        self.check_macro_params(f, decl);
        if let (Some(t), Some(ret)) = (f.ret_type().and_then(|r| r.ty()), &decl.ret)
            && result_form(ret).is_none()
            && !holds_error(ret)
        {
            let at = self.at(t.syntax());
            self.malformed(at, "gives `meta.Expr`, `meta.Pattern` or `meta.Type`");
        }
        self.check_macro_row(f, decl);
    }

    /// macros.procedural-declarations's parameters: each of an input type, and `meta.Tokens` only
    /// last.
    fn check_macro_params(&mut self, f: &ast::Fn, decl: &FnDecl) {
        let Some(params) = f.param_list() else { return };
        if let Some(s) = params.self_param() {
            let at = s
                .self_token()
                .map_or_else(|| self.at(s.syntax()), |t| self.at_token(&t));
            self.malformed(at, "takes no `self`");
        }
        let written: Vec<ast::Param> = params.params().collect();
        let types = decl.params.iter().filter_map(|p| match p {
            Param::Param(_, t, _) => Some(t),
            Param::SelfParam(..) => None,
        });
        let last = written.len().saturating_sub(1);
        for (i, (p, ty)) in written.iter().zip(types).enumerate() {
            let at = p
                .ty()
                .map_or_else(|| self.at(p.syntax()), |t| self.at(t.syntax()));
            match Input::of(ty) {
                _ if holds_error(ty) => {}
                None => {
                    let shown = p
                        .ty()
                        .map(|t| t.syntax().text().to_string())
                        .unwrap_or_default();
                    let message = format!(
                        "a macro takes no `{shown}`: its parameters take `meta.Expr`, \
                         `meta.Pattern`, `meta.Type`, `meta.Text`, `meta.File` or `meta.Tokens`"
                    );
                    self.error(codes::E0228, at, message);
                }
                Some(Input::Tokens) if i < last => {
                    self.malformed(at, "takes `meta.Tokens` only in its last parameter");
                }
                Some(_) => {}
            }
        }
    }

    /// macros.procedural-declarations's row: empty, or `raise<meta.Error>`.
    fn check_macro_row(&mut self, f: &ast::Fn, decl: &FnDecl) {
        let Some(row) = f.row() else { return };
        for element in row.elements() {
            let at = self.at(element.syntax());
            match element {
                ast::RowElem::RowRaise(_) => {
                    let fits = decl
                        .row
                        .raise
                        .as_deref()
                        .is_none_or(|t| is_meta_error(t) || holds_error(t));
                    if !fits {
                        self.malformed(at, "raises only `meta.Error`");
                    }
                }
                ast::RowElem::RowIo(_) | ast::RowElem::RowAsync(_) => {
                    self.malformed(at, "performs nothing");
                }
                ast::RowElem::RowVar(v) => {
                    let at = v.ident().map_or(at, |t| self.at_token(&t));
                    self.malformed(at, "has no row variable");
                }
                ast::RowElem::RowEffect(e) => {
                    let first = e.path().and_then(|p| p.segments().next());
                    let at = first.map_or(at, |t| self.at_token(&t));
                    self.malformed(at, "performs nothing");
                }
            }
        }
    }

    fn malformed(&mut self, at: TextRange, what: &str) {
        self.error(codes::E0228, at, format!("a macro {what}"));
    }
}

/// Whether a type holds the error type, which another diagnostic reports.
pub(crate) fn holds_error(t: &Ty) -> bool {
    match t {
        Ty::Error => true,
        Ty::Con(_, args) | Ty::Tuple(args) | Ty::App(_, args) => args.iter().any(holds_error),
        Ty::Fn(f) => {
            f.params.iter().any(|(_, t)| holds_error(t))
                || f.ret.as_ref().is_some_and(holds_error)
                || f.row.raise.as_deref().is_some_and(holds_error)
        }
        Ty::Spread(_, t) => holds_error(t),
        Ty::Handler(h) => h.effect.args.iter().chain(&h.answer).any(holds_error),
        Ty::Param(_) | Ty::SelfTy | Ty::Value(_) => false,
    }
}
