//! handlers.resume-at-most-once: an operation's body of a handler that takes control resumes at
//! most once on each path: never in a loop or a closure literal, never twice in sequence, and never
//! in a branch after another branch that resumed.

use stilt_diag::{Diagnostic, codes};
use stilt_hir::hir::BinaryOp;
use stilt_syntax::TextRange;

use crate::tast::walk;
use crate::tast::{Block, Expr, ExprKind};

const MESSAGE: &str = "this may resume a second time, but a handler resumes at most once on each \
                       path, so that no continuation is copied";

/// Every `resume` in `e`, outside the handler literals in it, whose own operations [`errors`]
/// checks.
fn resumes(e: &Expr, found: &mut Vec<TextRange>) {
    match &e.kind {
        ExprKind::Resume(x) => {
            found.push(e.at);
            if let Some(x) = x {
                resumes(x, found);
            }
        }
        ExprKind::Handler(_) => {}
        _ => walk::children(e)
            .into_iter()
            .for_each(|x| resumes(x, found)),
    }
}

/// Follows `e` in evaluation order and tells whether a path through it may have resumed by its
/// end, given `resumed` before it, reporting each `resume` that may run after another. A
/// `return`, `break`, `continue` or `raise` ends its path.
fn flow(report: &mut Vec<TextRange>, resumed: bool, e: &Expr) -> bool {
    let seq = |report: &mut Vec<TextRange>, r: bool, es: Vec<&Expr>| {
        es.into_iter().fold(r, |r, x| flow(report, r, x))
    };
    match &e.kind {
        ExprKind::Resume(x) => {
            if seq(report, resumed, x.iter().map(|x| &**x).collect()) {
                report.push(e.at);
            }
            true
        }
        ExprKind::Handler(_) => resumed,
        // A `resume` in a loop or a closure literal may run twice.
        ExprKind::Closure(..) | ExprKind::Loop(_) | ExprKind::While(..) | ExprKind::For(..) => {
            resumes(e, report);
            resumed
        }
        ExprKind::If(c, b, alt) | ExprKind::IfLet(_, c, b, alt) => {
            let r = flow(report, resumed, c);
            let taken = seq(report, r, walk::block_exprs(b));
            let other = alt.as_deref().map_or(r, |a| flow(report, r, a));
            taken || other
        }
        ExprKind::Match(s, arms) => branches(report, resumed, s, arms),
        ExprKind::Try(s, Some(c)) => branches(report, resumed, s, &c.arms),
        ExprKind::Else(a, b) | ExprKind::Binary(BinaryOp::And | BinaryOp::Or, a, b) => {
            // The right operand is followed whether or not the left one resumed, so that its
            // `resume`s are reported.
            let r = flow(report, resumed, a);
            let right = flow(report, r, b);
            r || right
        }
        ExprKind::Return(x) => {
            seq(report, resumed, x.iter().map(|x| &**x).collect());
            false
        }
        ExprKind::Raise(x) => {
            flow(report, resumed, x);
            false
        }
        ExprKind::Break | ExprKind::Continue => false,
        _ => seq(report, resumed, walk::children(e)),
    }
}

/// The arms of a `match` or a `catch` after `s`, each a path of its own.
fn branches(
    report: &mut Vec<TextRange>,
    resumed: bool,
    s: &Expr,
    arms: &[crate::tast::Arm],
) -> bool {
    let r = flow(report, resumed, s);
    arms.iter().fold(r, |any, a| {
        let g = a.guard.iter().fold(r, |r, g| flow(report, r, g));
        flow(report, g, &a.body) || any
    })
}

/// E0514 at each `resume` of a body that may run a second time, in source order.
pub(super) fn errors(block: &Block) -> Vec<Diagnostic> {
    let mut found = Vec::new();
    walk::exprs_of_block(block, &mut |e| {
        if let ExprKind::Handler(h) = &e.kind
            && h.control
        {
            for (_, op) in &h.ops {
                if let ExprKind::Closure(_, body) = &op.kind {
                    flow(&mut found, false, body);
                }
            }
        }
    });
    found.sort_by_key(|at| at.start());
    found.dedup_by_key(|at| at.start());
    found
        .into_iter()
        .map(|at| Diagnostic::new(codes::E0514, at, MESSAGE))
        .collect()
}
