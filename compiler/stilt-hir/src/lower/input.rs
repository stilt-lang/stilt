//! An input of the REPL, resolved in its module's scope with the session's bindings in scope
//! (repl.scope and repl.input-checking).
//!
//! The input is a body of its own, whose parameters are the bindings, in the order they were
//! bound, so that each binding resolves to its parameter, ahead of the module's items, as a
//! local of a body does. Its positions are the input's own, counted from its first byte.

use stilt_db::{Db, Program, SourceFile};
use stilt_diag::Diagnostic;
use stilt_syntax::TextRange;
use stilt_syntax::ast::{self, AstNode as _};

use super::{Ctx, Resolver};
use crate::hir::{Body, BodyValue, Expr, ExprKind, Ident, LocalId, Name, Stmt, StmtKind};
use crate::scope::modules_of;

/// An input, resolved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Input {
    /// Its body: a parameter for each binding, then the input's statement. A `let`'s body ends
    /// with the names the `let` binds, in order: the one it binds, or a tuple of them.
    pub body: Body,
    /// Its errors of name resolution.
    pub diagnostics: Vec<Diagnostic>,
    /// The names that a `let` binds, in order, with their locals.
    pub bound: Vec<(Name, LocalId)>,
}

/// Resolves `stmt`, a `let` or an expression statement, in the module of `file`, with a
/// parameter for each of `bindings`, in order.
///
/// # Panics
///
/// Panics when `file` is no file of the program or of the standard library.
#[must_use]
pub fn resolve_input(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    bindings: &[Name],
    stmt: &ast::Stmt,
) -> Input {
    let map = modules_of(db, program, file);
    let module = map
        .of_file(file)
        .expect("every file of the program has a module");
    let mut r = Resolver::new(db, program, map, module, file);
    // An input is a body, so each name it doesn't resolve is reported once (errors.unknown-names).
    let ((stmts, params, bound), held, analysed) = r.body_code(|r| r.input(bindings, stmt));
    let whole = r.at(stmt.syntax());
    let body = Body {
        locals: r.locals,
        params,
        value: BodyValue::Block(stmts),
        at: whole,
        has_errors: !r.diagnostics.is_empty() || !held.is_empty(),
        signature: None,
        limits: Vec::new(),
        held,
        analysed,
        fixed: Vec::new(),
        expansions: std::mem::take(&mut r.expansions),
        unsafe_blocks: std::mem::take(&mut r.unsafe_blocks),
    };
    Input {
        body,
        diagnostics: r.diagnostics,
        bound,
    }
}

impl Resolver<'_> {
    /// The statements of an input's body, its parameters, and the names its `let` binds.
    fn input(
        &mut self,
        bindings: &[Name],
        stmt: &ast::Stmt,
    ) -> (Vec<Stmt>, Vec<LocalId>, Vec<(Name, LocalId)>) {
        let params: Vec<LocalId> = bindings
            .iter()
            .map(|name| {
                let id = self.fresh(&Ident {
                    name: *name,
                    at: TextRange::default(),
                });
                self.scope.push((*name, Some(id)));
                id
            })
            .collect();
        let depth = self.scope.len();
        let first = self.stmt(&Ctx::module(), stmt);
        let at = first.at;
        let mut stmts = vec![first];
        let ast::Stmt::LetStmt(_) = stmt else {
            return (stmts, params, Vec::new());
        };
        let bound: Vec<(Name, LocalId)> = self.scope[depth..]
            .iter()
            .filter_map(|(name, v)| Some((*name, (*v)?)))
            .collect();
        stmts.push(Stmt {
            kind: StmtKind::Expr(names(&bound, at)),
            at,
        });
        (stmts, params, bound)
    }
}

/// The value of the names a `let` binds: the one it binds, or a tuple of them, `()` for none.
fn names(bound: &[(Name, LocalId)], at: TextRange) -> Expr {
    let local = |id: LocalId| Expr {
        kind: ExprKind::Local(id),
        at,
    };
    match bound {
        [(_, id)] => local(*id),
        _ => Expr {
            kind: ExprKind::Tuple(bound.iter().map(|(_, id)| local(*id)).collect()),
            at,
        },
    }
}
