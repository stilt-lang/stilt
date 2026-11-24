//! handlers.with-pairing: a `with` handles every performance of its effect that reaches it while
//! its block runs, so no call in the block may perform through a row variable of the enclosing
//! function, unless the callee's row holds the effect and the signature pairs the variable with it,
//! as effects.paired-row-variables and effects.passing-to-paired-variables pair a row variable with
//! an error type.

use stilt_diag::{Diagnostic, Fix, codes};
use stilt_hir::hir::Item;
use stilt_syntax::TextRange;

use super::marking::{callee_row, paired};
use super::signature::SigInfo;
use crate::tast::walk;
use crate::tast::{Block, Expr, ExprKind, Label};
use crate::ty::{RowParam, Ty};

/// The `with` of an effect, with its type arguments, whose block holds the calls checked.
struct Handled<'a> {
    sig: &'a SigInfo<'a>,
    pairs: &'a [(RowParam, Label)],
    effect: &'a Item,
    args: &'a [Ty],
}

/// E0516 at each call in a `with`'s block that performs through a row variable that the
/// signature doesn't pair with the handled effect. A call reaches the `with` unless it is
/// inside a closure literal or inside the block of a nearer `with` of the same effect.
pub(super) fn errors(
    sig: &SigInfo<'_>,
    pairs: &[(RowParam, Label)],
    block: &Block,
) -> Vec<Diagnostic> {
    let mut found = Vec::new();
    walk::exprs_of_block(block, &mut |e| {
        if let ExprKind::With(_, effect, args, b) = &e.kind {
            let h = Handled {
                sig,
                pairs,
                effect,
                args,
            };
            for x in walk::block_exprs(b) {
                inside(&h, x, &mut found);
            }
        }
    });
    found.sort_by_key(|d| (d.range.start(), d.message.clone()));
    found.dedup_by(|a, b| a.range.start() == b.range.start() && a.message == b.message);
    found
}

fn inside(h: &Handled<'_>, e: &Expr, found: &mut Vec<Diagnostic>) {
    if let Some(row) = callee_row(e) {
        let holds = row.effect(h.effect).is_some();
        let label = Label::Effect(h.effect.clone(), h.args.to_vec());
        let through = row
            .tail
            .params()
            .iter()
            .find(|p| !(holds && paired(h.pairs, p, &label)));
        if let Some(p) = through {
            found.push(handled(h, p, e.at));
        }
    }
    match &e.kind {
        ExprKind::Closure(..) => {}
        ExprKind::With(handler, effect, _, _) if effect == h.effect => inside(h, handler, found),
        _ => {
            for x in walk::children(e) {
                inside(h, x, found);
            }
        }
    }
}

/// E0516 at the call `at`, whose performances through `p` the `with` would handle. A
/// parameter's implicit row variable is fixed by naming the effect in the parameter's row, as
/// E0506 names the error type that a `catch` handles.
fn handled(h: &Handled<'_>, p: &RowParam, at: TextRange) -> Diagnostic {
    let name = h.sig.row_param_name(p);
    let effect = &h.effect.name;
    let Some(index) = SigInfo::passed_index(p) else {
        let message = format!(
            "the `with` around this call would also handle what it performs through `{name}`, \
             so pair them in your signature: `{{{effect}, {name}}}`"
        );
        return Diagnostic::new(codes::E0516, at, message);
    };
    let message =
        format!("`{name}`'s performances belong to the caller, but this `with` handles them");
    let d = Diagnostic::new(codes::E0516, at, message);
    let written = h.sig.written(&Ty::Con(h.effect.clone(), h.args.to_vec()));
    match written.and_then(|w| Some((h.sig.in_param_row(index, &w)?, w))) {
        Some((edits, w)) => d.with_fix(Fix::new(
            format!("handle `{name}`'s `{w}` here: write `{w}` in its row"),
            edits,
        )),
        None => d,
    }
}
