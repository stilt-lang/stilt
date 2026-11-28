//! The later phases of checking a body that type checking found no error in (errors.phases;
//! errors.phase-by-form): its marking and handling of raises, the parameters that escape, the
//! exhaustiveness of its arms, its modes, the one `yield` of a projection's paths, and the
//! implicit effects of functions that a `without` limits. Each reads the typed body.

pub(crate) mod demands;
mod escapes;
mod exhaustive;
mod handled;
pub(crate) mod implicit;
mod marking;
mod modes;
mod resumes;
mod signature;
mod staged;
pub(crate) mod unsafe_limit;
pub(crate) mod views;
mod yields;

use stilt_diag::{Diagnostic, codes};
use stilt_hir::decls::Lookup;

use crate::tast::walk;
use crate::tast::{Block, ExprKind, TypedBody};
use implicit::{Limited, Scope};
pub(crate) use signature::SigInfo;

/// declarations.typed-holes.
fn holes(block: &Block) -> Vec<Diagnostic> {
    let mut found = Vec::new();
    walk::exprs_of_block(block, &mut |e| {
        if e.kind == ExprKind::Hole {
            found.push(Diagnostic::new(
                codes::W0300,
                e.at,
                "this hole is code not written yet",
            ));
        }
    });
    found
}

/// The errors of the limits on a body's sites, each with what the closest rule of acceptance
/// needs (facts.closest-rule).
fn limit_errors(
    decls: &dyn Lookup,
    sig: &SigInfo<'_>,
    body: &TypedBody,
    limited: &Limited<'_>,
    scope: &Scope<'_>,
) -> Vec<Diagnostic> {
    let sites = implicit::code_sites(decls, scope).unwrap_or_default();
    let writer = crate::accept::text::Writer {
        decls,
        body,
        names: sig.names,
    };
    implicit::errors(limited, &sites, sig.line, &|n| writer.need(n, sig.line))
}

/// Phase 2's errors of a body, the block of a typed body without errors, and phase 3's
/// warnings if it has none (errors.phases), with `reflected`, its E0350 (meta.types-without-shape).
/// `sig` is what the body's signature says, and `limited` what limits the body when a
/// `without` does, with what finding its sites needs,
/// whose panics, allocations and operations that may not end are then errors. `held` gives
/// the implicit effects of the program for a body with a `when`, whose block may hold no site
/// of `locks` (shared.locks).
pub(crate) fn check(
    decls: &dyn Lookup,
    sig: &SigInfo<'_>,
    body: &TypedBody,
    block: &Block,
    limited: Option<(&Limited<'_>, &Scope<'_>)>,
    held: Option<(&implicit::Effects, &Scope<'_>)>,
    reflected: Vec<Diagnostic>,
) -> Vec<Diagnostic> {
    let (exhaustive_errors, unreachable) = exhaustive::check(decls, block);
    let mut errors = marking::errors(sig, &body.pairs, &body.passed, block);
    // meta.types-without-shape: the types without a shape given to functions that reflect.
    errors.extend(reflected);
    errors.extend(resumes::errors(block));
    errors.extend(escapes::errors(sig, body, block));
    errors.extend(exhaustive_errors);
    errors.extend(staged::errors(body, block));
    let sources = views::Sources::of(body, block);
    errors.extend(views::errors(sig, body, block, &sources));
    let params: Vec<_> = body
        .params
        .iter()
        .map(|(_, v)| *v)
        .zip(sig.params.iter().map(|(_, at)| *at))
        .collect();
    errors.extend(demands::errors(
        decls,
        &body.locals,
        &params,
        &sources,
        block,
    ));
    let exclusivity = modes::Body {
        locals: &body.locals,
        params: &body.params,
        sources: &sources,
        end: sig.end(block),
        text: sig.text,
    };
    errors.extend(modes::errors(&exclusivity, block));
    if sig.projection {
        errors.extend(yields::errors(block, sig.end(block)));
    }
    if let Some((limited, scope)) = limited {
        errors.extend(limit_errors(decls, sig, body, limited, scope));
    }
    if let Some((effects, scope)) = held {
        let sites = implicit::code_sites(decls, scope).unwrap_or_default();
        errors.extend(implicit::locks::errors(
            *scope.module,
            effects,
            &sites,
            block,
        ));
    }
    if !errors.is_empty() {
        return errors;
    }
    // patterns.unreachable-arms: an arm that can never match gets only that warning.
    let dead = |d: &Diagnostic| {
        unreachable
            .iter()
            .any(|u| u.range.start() == d.range.start())
    };
    let mut warnings: Vec<Diagnostic> = marking::warnings(block)
        .into_iter()
        .filter(|d| !(d.code == codes::W0501 && dead(d)))
        .collect();
    warnings.extend(unreachable);
    warnings.extend(holes(block));
    warnings
}
