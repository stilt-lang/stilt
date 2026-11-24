//! Views where the types of a body put them (views.viewable-types and views.view-types): `View.of`
//! and `View.all` of a value that isn't viewable, E0420 at the argument, and a value that stores a
//! view, E0421 at the expression that builds it: a list, a tuple, a record or a variant holding
//! one, or a call whose result does, as `collect` on an `Iter<View<str>>` gives (views.consumers),
//! each reported where it is first built rather than where a value built so is used again.

use stilt_diag::{Diagnostic, codes};

use super::super::signature::SigInfo;
use super::Sources;
use crate::tast::walk;
use crate::tast::{Block, Callee, Expr, ExprKind, StmtKind};
use crate::ty::{Ty, is_prelude, is_view_type};

/// The errors of views.viewable-types and views.view-types in a body.
pub(super) fn errors(sig: &SigInfo<'_>, block: &Block, found: &Sources) -> Vec<Diagnostic> {
    // The value of a `let` whose written type is E0421 has its view type from there, where it
    // is reported.
    let mut written = Vec::new();
    walk::iter_block(
        block,
        &mut |s| {
            if let StmtKind::Let(b) | StmtKind::Var(b) = &s.kind
                && sig.analysed.iter().any(|d| s.at.contains_range(d.range))
            {
                written.push(b.value.at);
            }
        },
        &mut |_| {},
    );
    let mut errors = Vec::new();
    walk::exprs_of_block(block, &mut |e| {
        errors.extend(not_viewable(sig, e));
        let held = stores(e) || holds_captured(e, found);
        if builds(e) && held && !written.contains(&e.at) {
            errors.push(stored(e));
        }
    });
    errors
}

/// E0420 for `View.of` or `View.all` of a value that isn't viewable, at the value.
fn not_viewable(sig: &SigInfo<'_>, e: &Expr) -> Option<Diagnostic> {
    let ExprKind::Call(Callee::Member(owner, name), _, args, _) = &e.kind else {
        return None;
    };
    if !is_view_type(owner, "View") || !matches!(&**name, "of" | "all") {
        return None;
    }
    let source = &args.first()?.value;
    if source.ty.is_viewable() {
        return None;
    }
    let shown = sig.show(&source.ty);
    let message = format!("`{shown}` can't be viewed: only a `str` or a `List` can");
    Some(Diagnostic::new(codes::E0420, source.at, message))
}

/// Whether an expression builds a value, rather than reading one built elsewhere.
/// A call whose first argument a demand on the thread axes checks, as `Shared.new`'s, is left
/// to that check (shared.tasks-and-modes; `demands`).
fn builds(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Construct(item, ..) => !is_prelude(item, "Some"),
        ExprKind::Call(callee, ..) => !super::super::demands::demanded(callee, 0),
        ExprKind::List(_)
        | ExprKind::Tuple(_)
        | ExprKind::Record(..)
        | ExprKind::Project(..)
        | ExprKind::CallValue(..) => true,
        _ => false,
    }
}

/// Whether an expression's value stores a view while none of the values it is built from does,
/// which would be where the view was first stored.
fn stores(e: &Expr) -> bool {
    e.ty.stores_view() && !walk::children(e).iter().any(|c| c.ty.stores_view())
}

/// Whether a list, a tuple, a record or a variant holds a closure that captures a view, a view
/// type of its own (views.view-types), which its type doesn't tell.
fn holds_captured(e: &Expr, found: &Sources) -> bool {
    let parts: Vec<&Expr> = match &e.kind {
        ExprKind::List(es) | ExprKind::Tuple(es) | ExprKind::Construct(_, _, es) => {
            es.iter().collect()
        }
        ExprKind::Record(_, _, fields) => fields.iter().map(|(_, x)| x).collect(),
        _ => return false,
    };
    parts
        .into_iter()
        .any(|x| matches!(x.ty, Ty::Fn(_)) && !found.sources(x).is_empty())
}

/// E0421 at an expression that builds a value that stores a view.
fn stored(e: &Expr) -> Diagnostic {
    let what = match &e.kind {
        ExprKind::List(_) => "a list",
        ExprKind::Tuple(_) => "a tuple",
        ExprKind::Record(..) => "a record",
        ExprKind::Construct(..) => "a variant",
        _ => "this call's result",
    };
    let message = format!("{what} can't hold a view, which must not outlive what it views");
    Diagnostic::new(codes::E0421, e.at, message)
}
