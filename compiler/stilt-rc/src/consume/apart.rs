//! The parameters that a function takes apart to build in their place (values.consumed-parameters):
//! a `match` or an `if let` on the parameter itself, a value of a recursive type, with a pattern of
//! one of its variants with a payload, in an arm whose code builds a value of a variant with a
//! payload of the same type. The function consumes such a parameter, so that a caller that passes
//! its last use gives up the memory of the variant it matched, which the arm can build in.
//!
//! The rule reads the typed body, since the types it names are gone from the MIR; reference
//! counting then finds where the memory of a matched value can be used again (`crate::reuse`).

use stilt_db::{Db, Program};
use stilt_hir::decls::{Lookup, QueriedOnce};
use stilt_hir::hir::{Item, LocalId, Mode, Name};
use stilt_mir::{Code, FnRef, code_of};
use stilt_types::is_recursive;
use stilt_types::tast::walk::{self, Part};
use stilt_types::tast::{Block, Code as Body, Definition, Expr, ExprKind, Pat, PatKind};

/// The names of the parameters of `f` that its body takes apart to build in their place.
pub(crate) fn taken_apart(db: &dyn Db, program: Program, f: &FnRef) -> Vec<Name> {
    let Some(Code::Body(file, index)) = code_of(db, program, f.generic().clone()) else {
        return Vec::new();
    };
    let typed = &stilt_types::infer_body(db, program, file, index).body;
    let Definition::Code(code) = &typed.code else {
        return Vec::new();
    };
    let params: Vec<LocalId> = typed
        .params
        .iter()
        .filter(|(mode, _)| *mode == Mode::Let)
        .map(|(_, v)| *v)
        .collect();
    let decls = QueriedOnce::new(db, program);
    let mut found: Vec<LocalId> = Vec::new();
    let mut look = |e: &Expr| {
        let Some(v) = rebuilt(&decls, e) else { return };
        if params.contains(&v) && !found.contains(&v) {
            found.push(v);
        }
    };
    match code {
        Body::Block(b) => walk::exprs_of_block(b, &mut look),
        Body::Expr(e) => walk::iter(e, &mut |_| {}, &mut look),
    }
    found
        .into_iter()
        .map(|v| typed.locals[v.0 as usize])
        .collect()
}

/// The local that a `match` or an `if let` takes apart to build in its place, if `e` is one
/// that does.
fn rebuilt(decls: &dyn Lookup, e: &Expr) -> Option<LocalId> {
    let (scrutinee, arms): (&Expr, Vec<(&Pat, Part<'_>)>) = match &e.kind {
        ExprKind::Match(scrutinee, arms) => (
            scrutinee,
            arms.iter()
                .map(|a| (&a.pattern, Part::Expr(&a.body)))
                .collect(),
        ),
        ExprKind::IfLet(pattern, scrutinee, block, _) => {
            (scrutinee, vec![(pattern, Part::Block(block))])
        }
        _ => return None,
    };
    let ExprKind::Local(v) = scrutinee.kind else {
        return None;
    };
    arms.into_iter()
        .any(|(pattern, code)| {
            matched(decls, pattern).is_some_and(|ty| match code {
                Part::Expr(e) => builds(decls, e, &ty),
                Part::Block(b) => builds_in(decls, b, &ty),
            })
        })
        .then_some(v)
}

/// The recursive type of the variant with a payload that a pattern matches, if it matches one,
/// itself or through one of its alternatives.
fn matched(decls: &dyn Lookup, p: &Pat) -> Option<Item> {
    match &p.kind {
        PatKind::Variant(item, payload) if !payload.is_empty() => {
            let ty = &decls.variant(item)?.ty;
            is_recursive(decls, ty).then(|| ty.clone())
        }
        PatKind::Or(alternatives) => alternatives.iter().find_map(|a| matched(decls, a)),
        _ => None,
    }
}

/// Whether code builds a value of a variant of `ty` with a payload, outside the closure literals
/// it holds, whose code runs elsewhere.
fn builds(decls: &dyn Lookup, e: &Expr, ty: &Item) -> bool {
    match &e.kind {
        ExprKind::Closure(..) => false,
        ExprKind::Construct(item, _, payload)
            if !payload.is_empty() && decls.variant(item).is_some_and(|v| v.ty == *ty) =>
        {
            true
        }
        _ => walk::parts(e).into_iter().any(|part| match part {
            Part::Expr(e) => builds(decls, e, ty),
            Part::Block(b) => builds_in(decls, b, ty),
        }),
    }
}

/// [`builds`], for a block.
fn builds_in(decls: &dyn Lookup, b: &Block, ty: &Item) -> bool {
    walk::block_exprs(b)
        .into_iter()
        .any(|e| builds(decls, e, ty))
}
