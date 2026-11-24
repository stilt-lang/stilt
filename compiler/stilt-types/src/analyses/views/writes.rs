//! Views that must write (projections.writable-bindings): the view given to a `var` binding of
//! `View<T>`, assigned to the whole of one, or yielded by a projection without being a place
//! (projections.yield), writes every source it has, since the binding writes through it. Each view
//! that reads a source is E0428, at the view, naming the source, with the fixes the rule names:
//! make it with `view.into(inout xs, …)`, or bind it with `let`. Rule numbers in comments refer to
//! the Reference's projections chapter.

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_hir::hir::{LocalId, Mode, Name};
use stilt_syntax::{TextRange, TextSize};

use super::super::modes::places::place;
use super::Sources;
use super::sources::Source;
use crate::tast::walk;
use crate::tast::{Block, Expr, ExprKind, PatKind, Stmt, StmtKind};

/// The errors of projections.yield and projections.writable-bindings in a function's body.
pub(super) fn errors(locals: &[Name], block: &Block, found: &Sources) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    walk::iter_block(
        block,
        &mut |s| errors.extend(stmt(locals, found, block, s)),
        &mut |_| {},
    );
    errors
}

/// Whether the body modifies a part of the binding `v`: assigns to it, passes it `inout` or
/// calls a method that takes `inout self` on it, which `let` would make E0403.
fn modified(block: &Block, v: LocalId) -> bool {
    let rooted = |e: &Expr| place(e).is_some_and(|p| p.root == v);
    let (mut assigned, mut passed) = (false, false);
    walk::iter_block(
        block,
        &mut |s| {
            if let StmtKind::Assign(_, p, _) = &s.kind {
                assigned |= rooted(p);
            }
        },
        &mut |e| {
            if let ExprKind::Call(_, _, args, _)
            | ExprKind::Project(_, _, args, _)
            | ExprKind::CallValue(_, args) = &e.kind
            {
                passed |= args
                    .iter()
                    .any(|a| a.mode == Mode::Inout && rooted(&a.value));
            }
        },
    );
    assigned || passed
}

/// Where a binding is written `var`, if a statement is one: the keyword's range, for the fix
/// that binds with `let`.
fn var_keyword(s: &Stmt) -> Option<TextRange> {
    matches!(s.kind, StmtKind::Var(_)).then(|| TextRange::at(s.at.start(), TextSize::of("var")))
}

/// projections.writable-bindings: a `var` binding of `View<T>`, and a view assigned to one.
/// projections.yield: the `var` of a `yield` whose operand isn't a place. The fix that binds with
/// `let` is offered when the body doesn't modify the binding, which `let` would make E0403.
fn stmt(locals: &[Name], found: &Sources, block: &Block, s: &Stmt) -> Option<Diagnostic> {
    match &s.kind {
        StmtKind::Var(b) => {
            let PatKind::Bind(v) = b.pattern.kind else {
                return None;
            };
            if !b.pattern.ty.is_window() {
                return None;
            }
            let what = format!("`{}`", locals[v.0 as usize]);
            let keyword = var_keyword(s).filter(|_| !modified(block, v));
            must_write(locals, found, &what, &b.value, keyword)
        }
        StmtKind::Assign(None, target, value) => {
            let ExprKind::Local(v) = target.kind else {
                return None;
            };
            if !found.is_writable(v) {
                return None;
            }
            let what = format!("`{}`", locals[v.0 as usize]);
            must_write(locals, found, &what, value, None)
        }
        StmtKind::Yield(value)
            if value.ty.is_view() && place(value).is_none() && !value.rooted_in_projection() =>
        {
            must_write(locals, found, "a yielded view", value, None)
        }
        _ => None,
    }
}

/// E0428 at `value` if it reads a source, which `what` must write, with its fixes: make it
/// through `inout`, and bind it with `let` where `var` is written at `var`.
fn must_write(
    locals: &[Name],
    found: &Sources,
    what: &str,
    value: &Expr,
    var: Option<TextRange>,
) -> Option<Diagnostic> {
    let sources = found.sources(value);
    let read = sources.iter().find(|s| s.reads())?;
    let (name, bare) = match read {
        Source::Place(p) | Source::Written(p) => {
            let bare = p.name(locals).to_owned();
            (format!("`{bare}`"), bare)
        }
        Source::Temporary(_) => ("a value made in this statement".to_owned(), String::new()),
    };
    let message = format!("this view reads {name}, which {what} must write");
    let mut d = Diagnostic::new(codes::E0428, value.at, message);
    if let Some(fix) = into_fix(value, &bare) {
        d = d.with_fix(fix);
    }
    if let Some(keyword) = var {
        let fix = Fix::new("bind it with `let`", vec![Edit::replace(keyword, "let")]);
        d = d.with_fix(fix);
    }
    Some(d)
}

/// The fix that makes a view of the place `bare` through `inout`: `View.of(xs, …)` becomes
/// `view.into(inout xs, …)`, and `View.all(xs)` `view.into(inout xs, 0, xs.len())`.
fn into_fix(value: &Expr, bare: &str) -> Option<Fix> {
    let ExprKind::Call(crate::tast::Callee::Member(owner, name), _, args, _) = &value.kind else {
        return None;
    };
    if !crate::ty::is_view_type(owner, "View") || bare.is_empty() {
        return None;
    }
    let source = &args.first()?.value;
    place(source)?;
    let head = TextRange::new(value.at.start(), source.at.start());
    let edits = match (&**name, args.len()) {
        ("of", 3) => vec![
            Edit::replace(head, "view.into("),
            Edit::insert(source.at.start(), "inout "),
        ],
        ("all", 1) => vec![
            Edit::replace(head, "view.into("),
            Edit::insert(source.at.start(), "inout "),
            Edit::insert(source.at.end(), format!(", 0, {bare}.len()")),
        ],
        _ => return None,
    };
    Some(Fix::new(
        format!("make it with `view.into(inout {bare}, …)`"),
        edits,
    ))
}
