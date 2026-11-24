//! Marking and handling: every call that can raise is inside a `try` (effects.marking), no `catch`
//! catches what a row variable, written or implicit, raises (effects.catch, as
//! effects.catch-around-row-variables amends it), and a catch-all raises again, uses its error or
//! gives a reason (effects.catch-alls-need-reason).
//!
//! Rule numbers in comments refer to the Reference's effects chapter.

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::{TextRange, TextSize};

use super::signature::SigInfo;
use crate::tast::walk;
use crate::tast::{Arm, Block, Expr, ExprKind, Label, PatKind, StmtKind};
use crate::ty::{Row, RowParam, Ty};

/// The row that the callee of a call performs, if the expression is a call.
pub(super) fn callee_row(e: &Expr) -> Option<&Row> {
    match &e.kind {
        ExprKind::Call(_, _, _, row) | ExprKind::Project(_, _, _, row) => Some(row),
        ExprKind::CallValue(f, _) => match &f.ty {
            Ty::Fn(f) => Some(&f.row),
            _ => None,
        },
        _ => None,
    }
}

/// Whether the expression is a call whose callee's row raises.
fn raising_call(e: &Expr) -> bool {
    callee_row(e).is_some_and(Row::raises)
}

/// Whether the expression is a call that must be marked. A call that raises only the error
/// type needs no `try` (effects.error-type-raises).
fn needs_try(e: &Expr) -> bool {
    matches!(callee_row(e).and_then(|row| row.raise.as_deref()), Some(t) if *t != Ty::Error)
}

/// The guard and the body of an arm, in order.
fn arm_exprs(a: &Arm) -> impl Iterator<Item = &Expr> {
    a.guard.as_deref().into_iter().chain([&a.body])
}

/// effects.marking: every raising call sits inside the operand of a `try`, which may be outside the
/// closure literal that holds the call. A `catch`'s arms are outside its operand.
fn unmarked(block: &Block) -> Vec<Diagnostic> {
    let mut found = Vec::new();
    for e in walk::block_exprs(block) {
        visit(e, false, &mut found);
    }
    found
}

/// Reports the unmarked calls in `e`, which is inside a `try`'s operand if `marked`.
fn visit(e: &Expr, marked: bool, found: &mut Vec<Diagnostic>) {
    if needs_try(e) && !marked {
        // A `try` can start any expression, and marks all of it (effects.marking).
        let mark = Fix::new(
            "mark it with `try`",
            vec![Edit::insert(e.at.start(), "try ")],
        );
        let d = Diagnostic::new(
            codes::E0505,
            e.at,
            "this call can raise, but no `try` marks it",
        );
        found.push(d.with_fix(mark));
    }
    match &e.kind {
        ExprKind::Try(operand, catch) => {
            visit(operand, true, found);
            for a in walk::catch_arms(catch.as_ref()) {
                for x in arm_exprs(a) {
                    visit(x, marked, found);
                }
            }
        }
        _ => {
            for x in walk::children(e) {
                visit(x, marked, found);
            }
        }
    }
}

/// Whether the enclosing signature pairs the row variable `v` with the label `l`: an error type or
/// an effect (handlers.with-pairing). A pairing with the error type causes no error
/// (errors.error-type and errors.root-causes, errors.syntax-errors, errors.parts,
/// errors.invalid-source-text, errors.breaks, errors.resuming, errors.part-reports,
/// errors.broken-parts, errors.broken-blocks, errors.declarations-with-errors,
/// errors.error-type-raises, errors.unknown-names, errors.phases, errors.phase-by-form and
/// errors.warnings-with-errors).
pub(super) fn paired(pairs: &[(RowParam, Label)], v: &RowParam, l: &Label) -> bool {
    matches!(l, Label::Raise(Ty::Error)) || pairs.iter().any(|(w, m)| w == v && m == l)
}

/// The row variable through which a call may raise an error type that the arms of a `catch`
/// around it don't expect: the first of its callee's row that isn't paired with the row's
/// `raise<E>`, or any if the row has none (effects.catch-around-row-variables).
fn raises_through<'a>(pairs: &[(RowParam, Label)], e: &'a Expr) -> Option<&'a RowParam> {
    let row = callee_row(e)?;
    row.tail.params().iter().find(|v| match &row.raise {
        None => true,
        Some(t) => !paired(pairs, v, &Label::Raise((**t).clone())),
    })
}

/// The signature of the body, and what it pairs.
struct Context<'a> {
    sig: &'a SigInfo<'a>,
    pairs: &'a [(RowParam, Label)],
}

/// effects.catch-around-row-variables, row variables: a `catch` handles every raise that reaches it
/// while its operand runs, so no call in the operand may raise through a row variable. A call
/// reaches the `catch` unless it is inside a closure literal, which runs only through a call of its
/// own, or inside the operand of a nearer `catch`.
fn caught_row_variables(cx: &Context<'_>, block: &Block) -> Vec<Diagnostic> {
    let mut found = Vec::new();
    walk::exprs_of_block(block, &mut |e| {
        if let ExprKind::Try(x, Some(c)) = &e.kind {
            operand(cx, &c.error, x, &mut found);
        }
    });
    found
}

/// Reports the calls in `e`, inside the operand of a `catch` of the error type `error`, that
/// raise through a row variable.
fn operand(cx: &Context<'_>, error: &Ty, e: &Expr, found: &mut Vec<Diagnostic>) {
    if let Some(v) = raises_through(cx.pairs, e) {
        found.push(caught(cx, error, v, e.at));
    }
    match &e.kind {
        ExprKind::Closure(..) => {}
        ExprKind::Try(_, Some(c)) => {
            for x in c.arms.iter().flat_map(arm_exprs) {
                operand(cx, error, x, found);
            }
        }
        _ => {
            for x in walk::children(e) {
                operand(cx, error, x, found);
            }
        }
    }
}

/// E0506 at the call `at`, whose failures through `v` a `catch` of `error` would catch. A
/// parameter's implicit row variable is fixed by naming, in the parameter's row, the error type
/// that the `catch` handles, or a new type parameter when it handles none that can be written.
fn caught(cx: &Context<'_>, error: &Ty, v: &RowParam, at: TextRange) -> Diagnostic {
    let name = cx.sig.row_param_name(v);
    let Some(index) = SigInfo::passed_index(v) else {
        let message = format!(
            "the `catch` around this call would also catch what it raises through `{name}`"
        );
        return Diagnostic::new(codes::E0506, at, message);
    };
    let message =
        format!("`{name}`'s failures belong to the caller, but this `catch` catches them");
    let d = Diagnostic::new(codes::E0506, at, message);
    let known = (!matches!(error, Ty::Error) && *error != Ty::never())
        .then(|| cx.sig.written(error))
        .flatten();
    let (written, declare) = match known {
        Some(t) => (t, None),
        None => match cx.sig.new_type_param() {
            Some((n, edit)) => (n, Some(edit)),
            None => return d,
        },
    };
    let Some(mut edits) = cx.sig.raise_in_param(index, &written) else {
        return d;
    };
    edits.extend(declare);
    d.with_fix(Fix::new(
        format!(
            "handle `{name}`'s failures of type `{written}`: write `raise<{written}>` in its row"
        ),
        edits,
    ))
}

/// effects.passing-to-paired-variables: a use that gives a variable its callee pairs with `E` a row
/// holding a row variable of the enclosing function needs the enclosing signature to pair that
/// variable with `E` too. Each use is reported once, and not at all when it is a call that
/// effects.catch-around-row-variables already reports, at one of `caught`, since the same pairing
/// fixes both.
fn passed_on(
    cx: &Context<'_>,
    caught: &[TextSize],
    passed: &[(TextRange, Row, Label)],
) -> Vec<Diagnostic> {
    let mut unpaired: Vec<(TextRange, &RowParam, &Label)> = passed
        .iter()
        .filter(|(at, _, _)| !caught.contains(&at.start()))
        .filter_map(|(at, row, e)| {
            let v = row.tail.params().iter().find(|v| !paired(cx.pairs, v, e))?;
            Some((*at, v, e))
        })
        .collect();
    // The reference interpreter orders and merges uses by their position, which is where they start.
    let key = |x: &(TextRange, &RowParam, &Label)| (x.0.start(), x.1.clone(), show_label(cx, x.2));
    unpaired.sort_by_key(key);
    unpaired.dedup_by(|x, y| key(x) == key(y));
    unpaired
        .into_iter()
        .map(|(at, v, l)| match l {
            Label::Raise(e) => passed_unpaired(cx, at, v, e),
            Label::Effect(..) => passed_unhandled(cx, at, v, l),
        })
        .collect()
}

/// A label as a row writes it.
fn show_label(cx: &Context<'_>, l: &Label) -> String {
    match l {
        Label::Raise(t) => cx.sig.show(t),
        Label::Effect(e, args) => crate::ty::Table::default().show_effect(e, args, cx.sig.names),
    }
}

/// E0507 at the use `at`, which gives `v` to a variable paired with the effect `l`: one that
/// goes where the effect is handled (handlers.with-pairing).
fn passed_unhandled(cx: &Context<'_>, at: TextRange, v: &RowParam, l: &Label) -> Diagnostic {
    let name = cx.sig.row_param_name(v);
    let shown = show_label(cx, l);
    let message = format!(
        "`{name}` goes where `{shown}` is handled, so pair them in your signature: write \
         `{{{shown}, {name}}}` in one of its rows"
    );
    Diagnostic::new(codes::E0507, at, message)
}

/// E0507 at the use `at`, which gives `v` to a variable paired with `e`. A parameter's implicit
/// row variable is fixed by naming `e` in the parameter's row, when nothing pairs it yet.
fn passed_unpaired(cx: &Context<'_>, at: TextRange, v: &RowParam, e: &Ty) -> Diagnostic {
    let name = cx.sig.row_param_name(v);
    let shown = cx.sig.show(e);
    let Some(index) = SigInfo::passed_index(v) else {
        let message = format!(
            "`{name}` goes where only `{shown}` may be raised, so pair them in your signature: \
             write `{{raise<{shown}>, {name}}}` in one of its rows"
        );
        return Diagnostic::new(codes::E0507, at, message);
    };
    let message =
        format!("this takes `{name}`'s failures for a `{shown}`, but they belong to the caller");
    let d = Diagnostic::new(codes::E0507, at, message);
    let unpaired = !cx.pairs.iter().any(|(w, _)| w == v);
    let edits = cx
        .sig
        .written(e)
        .filter(|_| unpaired)
        .and_then(|t| Some((cx.sig.raise_in_param(index, &t)?, t)));
    match edits {
        Some((edits, t)) => d.with_fix(Fix::new(
            format!("say that `{name}` raises `{t}`: write `raise<{t}>` in its row"),
            edits,
        )),
        None => d,
    }
}

/// The errors in a body's marking and handling of raises: the calls that raise with no `try`
/// to mark them, the calls inside a `catch`'s operand that raise through a row variable whose
/// error type the `catch` doesn't expect, and the uses that pass a row variable on where its callee
/// pairs it with an error type that the body's signature doesn't pair it with
/// (effects.passing-to-paired-variables). `sig` names row variables and places fixes, `pairs` holds
/// what the body's signature pairs, and `passed` the uses that pass a row on to a pairing.
pub(crate) fn errors(
    sig: &SigInfo<'_>,
    pairs: &[(RowParam, Label)],
    passed: &[(TextRange, Row, Label)],
    block: &Block,
) -> Vec<Diagnostic> {
    let cx = Context { sig, pairs };
    let caught = caught_row_variables(&cx, block);
    let starts: Vec<TextSize> = caught.iter().map(|d| d.range.start()).collect();
    let mut found = unmarked(block);
    found.extend(caught);
    found.extend(super::handled::errors(sig, pairs, block));
    found.extend(passed_on(&cx, &starts, passed));
    found
}

/// effects.catch-alls-need-reason: a catch-all is an arm with no guard whose pattern is `_` or a
/// variable.
fn catch_all(a: &Arm) -> bool {
    a.guard.is_none() && matches!(a.pattern.kind, PatKind::Wild | PatKind::Bind(_))
}

/// Whether the arm's body is a `raise`, or a block that ends in one.
fn reraises(a: &Arm) -> bool {
    match &a.body.kind {
        ExprKind::Raise(_) => true,
        ExprKind::Block(stmts) => stmts.last().is_some_and(
            |s| matches!(&s.kind, StmtKind::Expr(e) if matches!(e.kind, ExprKind::Raise(_))),
        ),
        _ => false,
    }
}

/// Whether the arm's pattern is a variable that its body refers to, which shows, wraps or passes on
/// the error (effects.catch-alls-need-reason). A later binding of the same name is another local.
fn uses_error(a: &Arm) -> bool {
    let PatKind::Bind(error) = a.pattern.kind else {
        return false;
    };
    walk::exists(
        &a.body,
        &|e| matches!(e.kind, ExprKind::Local(l) if l == error),
    )
}

/// The warnings of effects.empty-try, about `try`s that mark nothing, and of
/// effects.catch-alls-need-reason, about catch-alls with neither a raise, a use of their error nor
/// a reason.
pub(crate) fn warnings(block: &Block) -> Vec<Diagnostic> {
    let mut found = Vec::new();
    let statements = statement_starts(block);
    // A `try` that is all of a statement goes with its `catch`, and leaves its operand as the
    // statement; elsewhere its operand, which runs to the end of the expression, might not.
    let empty = |try_: &Expr, operand: &Expr| {
        let d = Diagnostic::new(codes::W0500, try_.at, "nothing in this `try` can raise");
        if !statements.contains(&try_.at.start()) {
            return d;
        }
        // The `try` keyword before its operand, and the `catch` after it.
        let (start, end) = (try_.at.start(), try_.at.end());
        let keyword = TextRange::new(start, operand.at.start().clamp(start, end));
        let catch = TextRange::new(operand.at.end().clamp(start, end), end);
        let edits = [keyword, catch].into_iter().filter(|r| !r.is_empty());
        d.with_fix(Fix::new(
            "delete the `try`",
            edits.map(Edit::delete).collect(),
        ))
    };
    walk::exprs_of_block(block, &mut |e| match &e.kind {
        // An operand that holds an expression of the error type may raise it (errors.error-type).
        ExprKind::Try(operand, None) => {
            if !walk::exists(operand, &|e| raising_call(e) || e.ty == Ty::Error) {
                found.push(empty(e, operand));
            }
        }
        // No arm can run, which this warning already says.
        ExprKind::Try(operand, Some(c)) if c.handles_never() => found.push(empty(e, operand)),
        // A `catch` handles the error type with no diagnostic (effects.error-type-raises).
        ExprKind::Try(_, Some(c)) if c.error == Ty::Error => {}
        ExprKind::Try(_, Some(c)) => {
            for a in &c.arms {
                if catch_all(a) && !a.because && !reraises(a) && !uses_error(a) {
                    found.push(Diagnostic::new(
                        codes::W0501,
                        a.pattern.at,
                        "this arm catches every error and drops it, so it raises again, uses \
                         the error or gives a reason: `because \"…\"`",
                    ));
                }
            }
        }
        _ => {}
    });
    found
}

/// Where the expressions that are whole statements start, in the block and the blocks in it.
fn statement_starts(block: &Block) -> Vec<TextSize> {
    let mut starts = Vec::new();
    walk::iter_block(
        block,
        &mut |s| starts.extend(walk::stmt_exprs(s).iter().map(|e| e.at.start())),
        &mut |_| {},
    );
    starts
}

#[cfg(test)]
mod tests;
