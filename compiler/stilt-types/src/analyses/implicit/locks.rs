//! shared.locks: a `when` whose block has a site of `locks`, a `when` or a call of an item
//! that has it, the closure literals in the block included, is E0430 at the site, since holding one
//! value while waiting for another could deadlock. polymorphism.lazy-waits-for-nothing: so is the
//! function that `Lazy.new` keeps, E0435, since its value's computation must wait for nothing.

use std::collections::HashMap;

use stilt_diag::{Diagnostic, codes};
use stilt_syntax::TextRange;

use stilt_hir::hir::{LocalId, Name};

use super::limits::cause;
use super::{Effect, Effects, Site, Source};
use crate::tast::{Block, Callee, Expr, ExprKind, PatKind, StmtKind, walk};

/// The `when`s of a block, closures included, by where each is.
fn whens(block: &Block) -> Vec<TextRange> {
    let mut found = Vec::new();
    walk::exprs_of_block(block, &mut |e| {
        if matches!(e.kind, ExprKind::When(..)) {
            found.push(e.at);
        }
    });
    found
}

/// Whether a call's callee is `Lazy.new` of `std.lazy` (polymorphism.lazy-values).
fn is_lazy_new(callee: &Callee) -> bool {
    matches!(callee, Callee::Member(owner, name)
        if (&*owner.home, &*owner.name, &**name) == ("std.lazy", "Lazy", "new"))
}

/// Where the function that each call of `Lazy.new` in a block keeps is written: its argument,
/// or the closure literal that a `let` binds to the local its argument names.
fn lazy_functions(block: &Block) -> Vec<TextRange> {
    let mut closures: HashMap<LocalId, TextRange> = HashMap::new();
    walk::iter_block(
        block,
        &mut |s| {
            if let StmtKind::Let(b) = &s.kind
                && let PatKind::Bind(v) = b.pattern.kind
                && matches!(b.value.kind, ExprKind::Closure(..))
            {
                closures.insert(v, b.value.at);
            }
        },
        &mut |_| {},
    );
    let mut found = Vec::new();
    walk::exprs_of_block(block, &mut |e: &Expr| {
        if let ExprKind::Call(callee, _, args, _) = &e.kind
            && is_lazy_new(callee)
            && let Some(a) = args.first()
        {
            found.push(match a.value.kind {
                ExprKind::Local(v) => closures.get(&v).copied().unwrap_or(a.value.at),
                _ => a.value.at,
            });
        }
    });
    found
}

/// Whether a body's block has a `when` or a call of `Lazy.new`, so that its sites are needed
/// for [`errors`].
pub(crate) fn checks(block: &Block) -> bool {
    !whens(block).is_empty() || !lazy_functions(block).is_empty()
}

/// The errors of the sites of `locks` inside the `when`s of `block`, each site once, in the
/// order of the sites.
pub(crate) fn errors(
    module: Name,
    effects: &Effects,
    sites: &[Site],
    block: &Block,
) -> Vec<Diagnostic> {
    let whens = whens(block);
    let around = |at: TextRange| whens.iter().find(|w| **w != at && w.contains_range(at));
    let mut found: Vec<Diagnostic> = Vec::new();
    for site in sites {
        let (Some(outer), Some(source)) =
            (around(site.at), site.source(Effect::Locks, effects, None))
        else {
            continue;
        };
        if found.iter().any(|d| d.range == site.at) {
            continue;
        }
        let fact = match source {
            Source::Own(_) => "this `when` waits for its values".to_owned(),
            other => cause(module, effects, Effect::Locks, other),
        };
        let message =
            format!("{fact} while the `when` around it holds others, which could deadlock");
        let d = Diagnostic::new(codes::E0430, site.at, message);
        found.push(d.with_note(*outer, "this `when` holds its values for its whole block"));
    }
    lazy_errors(module, effects, sites, block, &mut found);
    found
}

/// E0435 at each site of `locks` in a function that `Lazy.new` keeps, once, unless E0430
/// reports it, in the order of the sites (polymorphism.lazy-waits-for-nothing).
fn lazy_errors(
    module: Name,
    effects: &Effects,
    sites: &[Site],
    block: &Block,
    found: &mut Vec<Diagnostic>,
) {
    let functions = lazy_functions(block);
    for site in sites {
        let (Some(function), Some(source)) = (
            functions.iter().find(|f| f.contains_range(site.at)),
            site.source(Effect::Locks, effects, None),
        ) else {
            continue;
        };
        if found.iter().any(|d| d.range == site.at) {
            continue;
        }
        let fact = match source {
            Source::Own(_) => "this `when` holds shared values".to_owned(),
            other => cause(module, effects, Effect::Locks, other),
        };
        let message =
            format!("a `Lazy`'s function must not wait, but {fact}; read them before `Lazy.new`");
        let d = Diagnostic::new(codes::E0435, site.at, message);
        found.push(d.with_note(
            *function,
            "`Lazy.new` computes its value with this function",
        ));
    }
}
