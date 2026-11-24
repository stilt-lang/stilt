//! `without unsafe` (c.without-unsafe): each `unsafe` block of a function's own code, which its
//! own `without unsafe` or its module's header limits, is E0204 at its `unsafe`. The limit
//! covers the function's own code alone, since no caller inherits the fact, and tests and doc
//! examples are exempt, as they are from every limit.

use stilt_diag::{Diagnostic, codes};
use stilt_hir::hir::{Body, Limit, Name};
use stilt_syntax::TextRange;

use crate::owners::BodyOwner;

/// The diagnostics `later` of the later phases of the body that `owner` owns, `body`, with,
/// for a function, the errors of its `unsafe` blocks under the limits `header` of its module's
/// header, where they are written in the file, and of its own `without`, relative to the
/// body's start. An error of `without unsafe` keeps the body's warnings back, as the other
/// errors of the later phases do.
pub(crate) fn with_errors(
    later: Vec<Diagnostic>,
    owner: &BodyOwner,
    header: &[(Limit, TextRange)],
    body: &Body,
) -> Vec<Diagnostic> {
    let BodyOwner::Fn { name, .. } = owner else {
        return later;
    };
    let errors = errors(*name, header, body);
    let none = errors.is_empty();
    (later.into_iter().filter(|d| none || d.is_error()))
        .chain(errors)
        .collect()
}

fn errors(function: Name, header: &[(Limit, TextRange)], body: &Body) -> Vec<Diagnostic> {
    let find = |limits: &[(Limit, TextRange)]| {
        limits
            .iter()
            .find_map(|(l, at)| (*l == Limit::Unsafe).then_some(*at))
    };
    let fact = "this `unsafe` block may run C code and break the language's guarantees";
    let (says, at, in_file) = match (find(&body.limits), find(header)) {
        (Some(at), _) => (format!("`{function}` says"), at, false),
        (None, Some(at)) => ("the module's header says".to_owned(), at, true),
        (None, None) => return Vec::new(),
    };
    body.unsafe_blocks
        .iter()
        .map(|b| {
            let message = format!("{fact}, but {says} `without unsafe`");
            let d = Diagnostic::new(codes::E0204, b.at, message);
            if in_file {
                d.with_note_in_file(at, "the limit")
            } else {
                d.with_note(at, "the limit")
            }
        })
        .collect()
}
