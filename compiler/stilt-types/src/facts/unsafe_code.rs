//! The facts `unsafe` and `foreign` of a function (c.unsafe-and-foreign): the `unsafe` blocks of
//! its own code, a closure literal's included, each with its reason, and the foreign functions its
//! own code names, each where it names one. Neither is inherited, so a caller of a function that
//! has them has neither.

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::body_starts;
use stilt_hir::decls::{Lookup, QueriedOnce};
use stilt_hir::hir::Name;
use stilt_syntax::TextRange;

use crate::queries::infer_body;
use crate::tast::walk::{iter, iter_block};
use crate::tast::{Callee, Code, Definition, ExprKind};

/// The `unsafe` blocks of a body, each with where its `unsafe` is in its file and its reason, in
/// the order they start. A body with an error has none.
#[must_use]
pub fn unsafe_blocks(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    index: u32,
) -> Vec<(TextRange, String)> {
    if matches!(
        infer_body(db, program, file, index).body.code,
        Definition::Broken
    ) {
        return Vec::new();
    }
    let start = body_starts(db, program, file)[index as usize];
    let hir = stilt_hir::module_body(db, program, file, index);
    (hir.unsafe_blocks.iter())
        .map(|b| (b.at + start, b.reason.clone()))
        .collect()
}

/// The foreign functions a body names, each with where it names one in its file, in the order
/// of the body. A body with an error names none.
#[must_use]
pub fn foreign_uses(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    index: u32,
) -> Vec<(TextRange, Name, stilt_hir::hir::Limits)> {
    let typed = &infer_body(db, program, file, index).body;
    let Definition::Code(code) = &typed.code else {
        return Vec::new();
    };
    let decls = QueriedOnce::new(db, program);
    let start = body_starts(db, program, file)[index as usize];
    let mut found = Vec::new();
    let mut each = |e: &crate::tast::Expr| {
        let (ExprKind::Call(Callee::Function(item), ..)
        | ExprKind::Callee(Callee::Function(item), _)) = &e.kind
        else {
            return;
        };
        if let Some(s) = decls.function(item).filter(|s| s.foreign) {
            found.push((e.at + start, item.name, s.trusted));
        }
    };
    match code {
        Code::Block(b) => iter_block(b, &mut |_| {}, &mut each),
        Code::Expr(e) => iter(e, &mut |_| {}, &mut each),
    }
    found
}
