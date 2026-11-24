//! Whether a typed body meets the error type (program.meeting-the-error-type): whether it has an
//! error of its own, or uses a declaration whose signature holds the error type. `run` replaces
//! such a body by a panic, since the error type has no values to run with.
//!
//! A body without an error of its own meets the error type only through what it uses: a call
//! or a name of a function or method whose signature holds it, a constant whose type holds it,
//! a value built of a type whose fields or payloads hold it, or such a field or payload read
//! or matched. Each of these leaves the error type in the type of some expression or pattern of
//! the body, except a call whose result type is free of it and a value built of such a type,
//! which are looked at for themselves.

use stilt_hir::decls::{FnSig, Lookup, TypeDefInfo};
use stilt_hir::hir::{self, Item};

use crate::tast::{
    Callee, Code, Definition, Expr, ExprKind, Pat, PatKind, Stmt, StmtKind, TypedBody, walk,
};
use crate::ty::Ty;

/// Whether a typed body meets the error type: it has an error that type checking found, or
/// one of its expressions or patterns has the error type, or it calls or builds what holds it.
#[must_use]
pub fn meets_error_type(decls: &dyn Lookup, body: &TypedBody) -> bool {
    match &body.code {
        Definition::Native => false,
        Definition::Broken => true,
        Definition::Code(Code::Block(block)) => {
            let (mut in_stmts, mut in_exprs) = (false, false);
            walk::iter_block(block, &mut |s| in_stmts |= stmt_meets(decls, s), &mut |e| {
                in_exprs |= expr_meets(decls, e);
            });
            in_stmts || in_exprs
        }
        Definition::Code(Code::Expr(e)) => exists(decls, e),
    }
}

/// Whether an expression or anything inside it meets the error type.
fn exists(decls: &dyn Lookup, e: &Expr) -> bool {
    let (mut in_stmts, mut in_exprs) = (false, false);
    walk::iter(e, &mut |s| in_stmts |= stmt_meets(decls, s), &mut |e| {
        in_exprs |= expr_meets(decls, e);
    });
    in_stmts || in_exprs
}

fn stmt_meets(decls: &dyn Lookup, s: &Stmt) -> bool {
    match &s.kind {
        StmtKind::Let(b) | StmtKind::Var(b) => pat_meets(decls, &b.pattern),
        StmtKind::Assign(..) | StmtKind::Assert(_) | StmtKind::Yield(_) | StmtKind::Expr(_) => {
            false
        }
    }
}

/// Whether an expression meets the error type itself, or through the patterns it holds. The
/// expressions inside it are looked at on their own.
fn expr_meets(decls: &dyn Lookup, e: &Expr) -> bool {
    if holds_error(&e.ty) {
        return true;
    }
    match &e.kind {
        ExprKind::Error => true,
        ExprKind::Call(callee, ..)
        | ExprKind::Project(callee, ..)
        | ExprKind::Callee(callee, _) => callee_meets(decls, callee),
        ExprKind::Record(item, ..) => type_meets(decls, item),
        ExprKind::Construct(variant, ..) | ExprKind::Constructor(variant, _) => decls
            .variant(variant)
            .is_some_and(|v| type_meets(decls, &v.ty)),
        ExprKind::Match(_, arms) => arms.iter().any(|a| pat_meets(decls, &a.pattern)),
        ExprKind::Try(_, Some(catch)) => {
            holds_error(&catch.error) || catch.arms.iter().any(|a| pat_meets(decls, &a.pattern))
        }
        ExprKind::Closure(params, _) => params.iter().any(|p| pat_meets(decls, p)),
        ExprKind::For(target, ..) | ExprKind::IfLet(target, ..) => pat_meets(decls, target),
        _ => false,
    }
}

fn pat_meets(decls: &dyn Lookup, p: &Pat) -> bool {
    if holds_error(&p.ty) {
        return true;
    }
    match &p.kind {
        PatKind::Error => true,
        PatKind::Const(e) => exists(decls, e),
        PatKind::Tuple(ps) | PatKind::Variant(_, ps) | PatKind::List(ps, _) | PatKind::Or(ps) => {
            ps.iter().any(|p| pat_meets(decls, p))
        }
        PatKind::Record(fields) => fields.iter().any(|(_, p)| pat_meets(decls, p)),
        PatKind::Wild | PatKind::Bind(_) | PatKind::Int(_) | PatKind::Str(_) | PatKind::Bool(_) => {
            false
        }
    }
}

/// Whether the signature of what a call names holds the error type. A trait method counts by
/// the trait's declaration of it, which the call is checked against: an impl's method with an
/// error of its own panics where it is called.
fn callee_meets(decls: &dyn Lookup, callee: &Callee) -> bool {
    match callee {
        Callee::Function(item) => decls.function(item).is_some_and(signature_holds_error),
        Callee::Member(owner, name) => decls
            .inherent_members(owner)
            .iter()
            .any(|m| m.name == *name && signature_holds_error(&m.signature)),
        Callee::TraitMethod(trait_item, name, _) => decls.trait_info(trait_item).is_some_and(|t| {
            t.methods
                .iter()
                .any(|m| m.name == *name && signature_holds_error(&m.signature))
        }),
        Callee::Operation(effect, name) => decls
            .effect_info(effect)
            .and_then(|info| info.op(name))
            .is_some_and(|(_, o)| {
                o.params.iter().any(|(_, t)| hir_holds_error(t))
                    || hir_holds_error(&o.ret)
                    || o.row.raise.as_deref().is_some_and(hir_holds_error)
            }),
    }
}

/// Whether the fields or payloads of a type hold the error type.
fn type_meets(decls: &dyn Lookup, item: &Item) -> bool {
    decls.type_info(item).is_some_and(|info| match &info.def {
        TypeDefInfo::Record(fields) => fields.iter().any(|(_, t)| hir_holds_error(t)),
        TypeDefInfo::Variants(variants) => {
            variants.iter().flat_map(|(_, p)| p).any(hir_holds_error)
        }
        TypeDefInfo::Builtin => false,
    })
}

/// Whether a signature's parameter types, return type or row hold the error type.
#[must_use]
pub fn signature_holds_error(s: &FnSig) -> bool {
    s.params.iter().any(|(_, t)| hir_holds_error(t))
        || hir_holds_error(&s.ret)
        || s.row.raise.as_deref().is_some_and(hir_holds_error)
}

/// Whether a type of a body holds the error type.
fn holds_error(t: &Ty) -> bool {
    match t {
        Ty::Error => true,
        Ty::Con(_, args) | Ty::Tuple(args) => args.iter().any(holds_error),
        Ty::Fn(f) => {
            f.params.iter().any(|(_, t)| holds_error(t))
                || holds_error(&f.ret)
                || f.row.raise.as_deref().is_some_and(holds_error)
        }
        Ty::Spread(s) => holds_error(&s.elem),
        Ty::Param(_) | Ty::Handler(_) | Ty::SelfTy | Ty::App(..) | Ty::Var(_) | Ty::Value(_) => {
            false
        }
    }
}

/// Whether a type of a declaration holds the error type.
#[must_use]
pub fn hir_holds_error(t: &hir::Ty) -> bool {
    match t {
        hir::Ty::Error => true,
        hir::Ty::Con(_, args) | hir::Ty::Tuple(args) | hir::Ty::App(_, args) => {
            args.iter().any(hir_holds_error)
        }
        hir::Ty::Fn(f) => {
            f.params.iter().any(|(_, t)| hir_holds_error(t))
                || f.ret.as_ref().is_some_and(hir_holds_error)
                || f.row.raise.as_deref().is_some_and(hir_holds_error)
        }
        hir::Ty::Spread(_, t) => hir_holds_error(t),
        hir::Ty::Handler(h) => h.effect.args.iter().chain(&h.answer).any(hir_holds_error),
        hir::Ty::Param(_) | hir::Ty::SelfTy | hir::Ty::Value(_) => false,
    }
}
