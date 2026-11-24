//! Whether a module uses the features of handlers to tasks that put it in the advanced tier
//! (handlers.advanced-tier; tasks.advanced-tier; program.module-tier): it
//! declares an effect, writes one or `async` in a row or a type, writes a handler, a `with` or a
//! `when`, performs an operation, or names `std.task` or `std.sync`. A module that only calls a
//! function declared elsewhere whose row holds no effect of its own stays in its tier, and nothing
//! in a macro's expansion counts (macros.advanced-tier).

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::body_starts;
use stilt_syntax::SyntaxKind::{
    EFFECT, HANDLER_EXPR, HANDLER_TYPE, ROW_ASYNC, ROW_EFFECT, WHEN_EXPR, WITH_EXPR,
};

use crate::queries::infer_body;
use crate::tast::{Callee, Code, Definition, ExprKind, walk};

/// Whether a file's module uses effects, handlers or tasks.
///
/// # Panics
///
/// If the module has 4G bodies or more.
#[must_use]
pub(super) fn uses_effects(db: &dyn Db, program: Program, file: SourceFile) -> bool {
    let written = stilt_db::parse(db, file).syntax().descendants().any(|n| {
        matches!(
            n.kind(),
            EFFECT | ROW_EFFECT | ROW_ASYNC | HANDLER_TYPE | HANDLER_EXPR | WITH_EXPR | WHEN_EXPR
        )
    });
    let names_tasks = stilt_hir::resolve_module(db, program, file)
        .references
        .iter()
        .any(|(m, _)| matches!(&**m, "std.task" | "std.sync"));
    let bodies = u32::try_from(body_starts(db, program, file).len()).expect("under 4G bodies");
    written || names_tasks || (0..bodies).any(|i| performs(db, program, file, i))
}

/// Whether the body `index` performs an operation outside every macro's expansion.
fn performs(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> bool {
    let expansions = &stilt_hir::module_body(db, program, file, index).expansions;
    let mut found = false;
    let mut expr = |e: &crate::tast::Expr| {
        found |= matches!(e.kind, ExprKind::Call(Callee::Operation(..), ..))
            && !super::in_expansion(expansions, e.at);
    };
    match &infer_body(db, program, file, index).body.code {
        Definition::Code(Code::Block(b)) => walk::iter_block(b, &mut |_| {}, &mut expr),
        Definition::Code(Code::Expr(e)) => walk::iter(e, &mut |_| {}, &mut expr),
        Definition::Native | Definition::Broken => {}
    }
    found
}
