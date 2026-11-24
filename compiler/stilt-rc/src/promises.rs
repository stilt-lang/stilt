//! The promises that read shared writes (facts.copy and facts.in-place-promise): `copy`, and the
//! writes and copies at calls that `without alloc` keeps in place only while modes.shared-writes
//! doesn't make them shared.
//!
//! `stilt-types` infers `panic`, `alloc` and `div`, and finds each body's sites, those that
//! wait on a modification's sharing among them. This module reads the shared writes that the
//! modes give each body, and finds what the sites of `stilt-types` leave: each site of `copy`, its
//! own or one it inherits (facts.copy and facts.without-copy), and each write or copy at a call
//! that allocates because it is shared (facts.writes-in-place and facts.copy-at-call). They are the
//! errors of the limits, E0204 where a `without` rules them out, and the causes that `show` prints.

mod reach;

use stilt_db::{Db, Program, SourceFile};
use stilt_diag::Diagnostic;
use stilt_hir::FileDiagnostic;
use stilt_syntax::TextRange;
use stilt_types::promises::{self, Body, Effect, Pending, Site, describe, through, verb};

use crate::modes::{Modification, SharedWrite};
use reach::{origin, reached, shared, shared_at};

/// A cause of `copy` or `alloc` that the shared writes give a body: its effect, where it is,
/// relative to the body's start, what it does as an error says it, and as `show` says it.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Finding {
    effect: Effect,
    at: TextRange,
    error: String,
    cause: String,
}

/// A shared modification, as messages name it: "this write to `ys` while `keep` shares it",
/// or with `a`, "a write to …"; the end of a `when`, which a later write to the handle's value
/// pays for, and a handle made of a binding's value that it may read after (modes.handles).
fn write(w: &SharedWrite, this: bool) -> String {
    let article = if this { "this" } else { "a" };
    let with = w.with.as_ref().map_or_else(
        || "a copy of it lasts".to_owned(),
        |k| format!("`{k}` shares it"),
    );
    let name = &w.name;
    match w.how {
        Modification::Write => format!("{article} write to `{name}` while {with}"),
        Modification::WhenEnd => format!(
            "the end of {article} `when`, which gives `{name}` back to its handle while {with},"
        ),
        Modification::NewHandle => {
            format!("{article} handle on `{name}`, which `{name}` may still read,")
        }
    }
}

/// An `inout` argument of an in-place parameter whose modification is shared, which the call
/// copies (facts.copy-at-call), as messages name it.
fn passing(p: &Pending, w: &SharedWrite, body: &Body, this: bool) -> String {
    let callee = p
        .callee
        .as_ref()
        .map_or_else(String::new, |k| describe(&body.module, k));
    let with = w.with.as_ref().map_or_else(
        || "a copy of it lasts".to_owned(),
        |k| format!("`{k}` shares it"),
    );
    if this {
        format!("passing `{}` to {callee} while {with}", w.name)
    } else {
        format!("a copy of `{}` for {callee} while {with}", w.name)
    }
}

/// What the shared writes give the body `index` of a file's module, of the effects `wanted`:
/// its causes of `copy`, and those of `alloc` that `stilt-types` can't see. Its shared writes,
/// and the fixed point of `copy`, are read only when they are wanted.
fn findings(
    db: &dyn Db,
    program: Program,
    (file, index): (SourceFile, u32),
    wanted: &[Effect],
) -> Vec<Finding> {
    let Some(body) = promises::body(db, program, file, index) else {
        return Vec::new();
    };
    let waits = body.sites.iter().any(|s| s.pending().is_some());
    let no_writes = Vec::new();
    let shared = if waits || wanted.contains(&Effect::Copy) {
        shared(db, program, body.key.clone())
    } else {
        &no_writes
    };
    let mut found = Vec::new();
    let mut matched: Vec<&SharedWrite> = Vec::new();
    for site in &body.sites {
        if let Some(p) = site.pending()
            && let Some(w) = shared_at(shared, p)
        {
            matched.push(w);
            let (error, cause) = match p.callee {
                Some(_) => (passing(p, w, &body, true), passing(p, w, &body, false)),
                None => (write(w, true), write(w, false)),
            };
            for effect in [Effect::Alloc, Effect::Copy] {
                found.push(finding(effect, site.at(), &error, &cause));
            }
            continue;
        }
        if let Some(fact) = site.copy() {
            found.push(finding(Effect::Copy, site.at(), &fact.this, &fact.a));
        }
        found.extend(named(db, program, &body, site, wanted));
    }
    for w in shared.iter().filter(|w| !matched.contains(w)) {
        found.push(finding(
            Effect::Copy,
            w.at,
            &write(w, true),
            &write(w, false),
        ));
    }
    found.retain(|f| wanted.contains(&f.effect));
    found.sort_by_key(|f| (f.at.start(), f.effect));
    found
}

fn finding(effect: Effect, at: TextRange, this: &str, a: &str) -> Finding {
    Finding {
        effect,
        at,
        error: format!("{this} {}", verb(effect)),
        cause: format!("{a} {}", verb(effect)),
    }
}

/// The causes of a site that names items: the first that copies shared data, and the first
/// that allocates only through a copy at a call that a shared modification makes.
fn named(
    db: &dyn Db,
    program: Program,
    body: &Body,
    site: &Site,
    wanted: &[Effect],
) -> Vec<Finding> {
    let mut found = Vec::new();
    for &effect in wanted {
        if effect == Effect::Alloc
            && site
                .names()
                .iter()
                .any(|k| promises::has(db, program, effect, k))
        {
            continue;
        }
        let reached = reached(db, program, effect);
        let Some(key) = site.names().iter().find(|k| reached.contains_key(*k)) else {
            continue;
        };
        let (from, operation) = origin(reached, key);
        let says = through(&body.module, effect, key, from, operation);
        found.push(Finding {
            effect,
            at: site.at(),
            error: says.clone(),
            cause: says,
        });
    }
    found
}

/// The causes of `copy` of the function of the body `index`, each where it is in its file and
/// what it does there (facts.copy and facts.visibility).
#[must_use]
pub fn copy_causes(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    index: u32,
) -> Vec<(Effect, TextRange, String)> {
    let start = stilt_hir::body_starts(db, program, file)[index as usize];
    findings(db, program, (file, index), &[Effect::Alloc, Effect::Copy])
        .into_iter()
        .map(|f| (f.effect, f.at + start, f.cause))
        .collect()
}

/// The errors of the limits on `copy` and `alloc` that the shared writes give the body `index`,
/// relative to its start. `run` replaces a body that has one by a panic, as any body with an
/// error (program.bodies-with-errors).
#[salsa::tracked(returns(ref))]
pub fn body_errors(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> Vec<Diagnostic> {
    let limits = promises::limits(db, program, file, index);
    if !limits.copy && !limits.alloc {
        return Vec::new();
    }
    let wanted: Vec<Effect> = [Effect::Alloc, Effect::Copy]
        .into_iter()
        .filter(|e| e.limited(limits))
        .collect();
    findings(db, program, (file, index), &wanted)
        .into_iter()
        .filter_map(|f| promises::limit_error(db, program, (file, index), f.effect, f.at, &f.error))
        .collect()
}

/// The program's diagnostics, as `stilt-types` checks them across the machine's cores, with
/// the errors of the limits that read shared writes, sorted as they are: by file, position and
/// code. A body whose part has a syntax error holds them back (errors.broken-parts).
#[must_use]
pub fn check_in_parallel<D: Db + Clone>(db: &D, program: Program) -> Vec<FileDiagnostic> {
    let mut all = stilt_types::check_in_parallel(db, program).to_vec();
    let before = all.len();
    for &file in stilt_db::reported_files(db, program) {
        let syntax = stilt_db::syntax_errors(db, file);
        let starts = stilt_hir::body_starts(db, program, file);
        for (index, &start) in (0..).zip(starts.iter()) {
            all.extend(
                body_errors(db, program, file, index)
                    .iter()
                    .map(|d| d.clone().shifted(start))
                    .filter(|d| !syntax.holds_back(d))
                    .map(|diagnostic| FileDiagnostic { file, diagnostic }),
            );
        }
    }
    if all.len() > before {
        all.sort_by(|a, b| {
            let key = |d: &FileDiagnostic| {
                (
                    d.file.path(db),
                    d.diagnostic.range.start(),
                    d.diagnostic.code,
                )
            };
            key(a).cmp(&key(b))
        });
    }
    all
}
