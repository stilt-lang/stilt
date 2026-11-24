//! Views and iterators (views.what-view-is and views.making-iterator), and writable views
//! (projections.writable-views): what a body does with them that the rules forbid. A `View` made of
//! a value that isn't viewable is E0420 (views.viewable-types), a view type where a value stores it
//! is E0421 (views.view-types), a view that leaves a scope that binds one of its sources, or the
//! function other than in its result, or in a result with a source that isn't a parameter, is E0422
//! (views.escaping), and a view that reads a source it must write, bound by `var`, yielded or
//! returned of an `inout` parameter, is E0428 (projections.writable-bindings and
//! projections.results-that-write). The sources each view reads and writes, which these and the
//! durations of modes.durations read (views.reads-that-last and views.change-while-viewed;
//! projections.what-view-writes), are found lexically ([`sources`]). The rules hold of a module of
//! any tier: a core module names no view type.

mod escapes;
mod scopes;
pub(crate) mod sources;
mod stored;
mod writes;

use stilt_diag::Diagnostic;

pub(crate) use super::modes::places::Place;
use super::signature::SigInfo;
use crate::tast::{Block, TypedBody};
pub(crate) use sources::Sources;

/// The errors of views.viewable-types, views.view-types and views.escaping in a function's body,
/// whose views have the sources `found`.
pub(crate) fn errors(
    sig: &SigInfo<'_>,
    body: &TypedBody,
    block: &Block,
    found: &Sources,
) -> Vec<Diagnostic> {
    let mut errors = sig.analysed.to_vec();
    errors.extend(stored::errors(sig, block, found));
    errors.extend(writes::errors(&body.locals, block, found));
    // A view that leaves a scope inside the function, and with it the function, is reported
    // where it leaves the scope.
    let scoped = scopes::errors(&body.locals, block, found);
    let escaped: Vec<Diagnostic> = escapes::errors(sig, body, block, found)
        .into_iter()
        .filter(|d| !scoped.iter().any(|s| s.range == d.range))
        .collect();
    errors.extend(scoped);
    errors.extend(escaped);
    errors
}
