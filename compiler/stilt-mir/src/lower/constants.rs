//! Which constants can be evaluated at any time (declarations.constant-evaluation and
//! declarations.constant-expressions): a constant is evaluated where the program first uses it, and
//! only a unary `-` that overflows can make its initializer panic, so a constant without one is
//! evaluated where it is convenient, as a read of it may be moved out of a loop.

use stilt_hir::hir::UnaryOp;
use stilt_types::infer_body;
use stilt_types::tast::{Code, Definition, Expr, ExprKind, StmtKind};

use super::Cx;
use crate::FnRef;
use crate::items::{Code as Where, code_of};

/// Whether evaluating the constant `f` can't panic, and so can't be told apart from
/// evaluating it earlier. A constant that refers to itself through others has an error, so it
/// is not safe.
pub(crate) fn cannot_panic(cx: &Cx<'_>, f: &FnRef) -> bool {
    safe(cx, f, &mut Vec::new())
}

fn safe(cx: &Cx<'_>, f: &FnRef, seen: &mut Vec<FnRef>) -> bool {
    if seen.contains(f) {
        return false;
    }
    seen.push(f.clone());
    let safe = match code_of(cx.db, cx.program, f.clone()) {
        Some(Where::Native) => true,
        Some(Where::Body(file, index)) => {
            match &infer_body(cx.db, cx.program, file, index).body.code {
                Definition::Code(Code::Expr(e)) => expr(cx, e, seen),
                Definition::Code(Code::Block(b)) => match b.as_slice() {
                    [s] => matches!(&s.kind, StmtKind::Expr(e) if expr(cx, e, seen)),
                    _ => false,
                },
                _ => false,
            }
        }
        None => false,
    };
    seen.pop();
    safe
}

/// Whether evaluating a constant expression can't panic. Anything that a constant expression
/// can't be built from counts as able to.
fn expr(cx: &Cx<'_>, e: &Expr, seen: &mut Vec<FnRef>) -> bool {
    match &e.kind {
        ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Constructor(..) => true,
        ExprKind::Unary(UnaryOp::Neg, x) => matches!(x.kind, ExprKind::Int(_)),
        ExprKind::Constant(item) => safe(cx, &FnRef::Const(item.clone()), seen),
        ExprKind::MemberConstant(owner, name, _) => {
            safe(cx, &FnRef::MemberConst(owner.clone(), *name), seen)
        }
        ExprKind::Construct(_, _, es) | ExprKind::Tuple(es) | ExprKind::List(es) => {
            es.iter().all(|e| expr(cx, e, seen))
        }
        ExprKind::Record(_, _, fields) => fields.iter().all(|(_, e)| expr(cx, e, seen)),
        _ => false,
    }
}
