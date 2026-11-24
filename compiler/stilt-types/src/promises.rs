//! What the checks of `copy` and of shared writes under `without alloc` read of the implicit
//! effects (facts.writes-in-place, facts.copy-at-call, facts.copy and facts.without-copy). They
//! need the shared writes of modes.shared-writes, which `stilt-rc` infers after this crate, so
//! this crate gives each body's sites, the effects it infers, the in-place parameters of the
//! program and the errors of the limits, and that crate checks the rest.

use stilt_db::{Db, Program, SourceFile};
use stilt_diag::Diagnostic;
use stilt_hir::decls::QueriedOnce;
use stilt_hir::hir::{Limits, Name};
use stilt_hir::{body_starts, header_limits, module_body};
use stilt_syntax::{TextRange, TextSize};

pub use crate::analyses::implicit::in_place::called;
use crate::analyses::implicit::in_place::causes;
use crate::analyses::implicit::{self, Limited};
pub use crate::analyses::implicit::{
    Effect, Fact, InPlace, Key, Pending, Site, describe, located, through, verb,
};
use crate::owners::BodyOwner;
pub use crate::queries::in_place_params;
use crate::queries::{
    body_limits, body_owner, implicit_effects, in_place_summary, module_info, scope,
};
use crate::tast::Definition;

/// A function's body, as the checks read it: its item, its module, its limits, its sites and
/// where it starts in its file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    /// Its item.
    pub key: Key,
    /// Its module.
    pub module: Name,
    /// What its `without` limits.
    pub limits: Limits,
    /// Its operations that have an effect themselves.
    pub sites: Vec<Site>,
    /// Where it starts in its file.
    pub start: TextSize,
}

/// The body `index` of a file's module, if it is a function's without an error
/// (facts.bodies-with-errors).
#[must_use]
pub fn body(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> Option<Body> {
    let module = module_info(db, program, file);
    let owner = body_owner(db, program, file, index);
    let key = owner.key(module.name)?;
    let scope = scope(db, program, file, index, Some(&key));
    if !matches!(scope.body.code, Definition::Code(_)) {
        return None;
    }
    let sites = implicit::code_sites(&QueriedOnce::new(db, program), &scope)?;
    Some(Body {
        limits: body_limits(module, owner),
        module: module.name,
        sites,
        start: body_starts(db, program, file)[index as usize],
        key,
    })
}

/// What limits the body `index` of a file's module: its own `without` and its module's.
#[must_use]
pub fn limits(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> Limits {
    body_limits(
        module_info(db, program, file),
        body_owner(db, program, file, index),
    )
}

/// Whether the item `key` has `effect`, as this crate infers it: `panic`, `alloc` or `div`.
#[must_use]
pub fn has(db: &dyn Db, program: Program, effect: Effect, key: &Key) -> bool {
    implicit_effects(db, program).has(effect, key)
}

/// The items that the check of `without alloc` in debug builds guards (facts.without-alloc).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AllocGuards {
    /// The items that a `without alloc` limits, through their own clause or their module's.
    pub limited: std::collections::BTreeSet<Key>,
    /// The items that allocate, which a limited item reaches only through a function value.
    pub allocating: std::collections::BTreeSet<Key>,
}

/// The items that the check of `without alloc` guards: none when no item is limited.
#[must_use]
pub fn alloc_guards(db: &dyn Db, program: Program) -> &AllocGuards {
    crate::queries::alloc_guards(db, program)
}

/// What an item that has `effect`, as this crate infers it, does, and through what.
#[must_use]
pub fn named(db: &dyn Db, program: Program, module: &Name, effect: Effect, key: &Key) -> String {
    let effects = implicit_effects(db, program);
    let (origin, operation) = effects.origin(effect, key);
    through(module, effect, key, origin, operation.map(|f| f.a.as_str()))
}

/// E0204 at `at`, relative to the start of the body `index`, where `fact` goes beyond the limit
/// on `effect`, if a `without` of the body's function or of its module has the limit.
#[must_use]
pub fn limit_error(
    db: &dyn Db,
    program: Program,
    (file, index): (SourceFile, u32),
    effect: Effect,
    at: TextRange,
    fact: &str,
) -> Option<Diagnostic> {
    let module = module_info(db, program, file);
    let owner = body_owner(db, program, file, index);
    let BodyOwner::Fn { name, .. } = owner else {
        return None;
    };
    let key = owner.key(module.name);
    let header = header_limits(db, program, file);
    let limited = Limited {
        module: &module.name,
        function: name,
        key: key.as_ref(),
        header,
        own: &module_body(db, program, file, index).limits,
        raises_str: false,
        effects: implicit_effects(db, program),
    };
    limited
        .limits(effect)
        .then(|| located(&limited, effect, at, fact))
}

/// The in-place parameters of the function of the body `index`, each with where, in its file,
/// a line makes it in place (facts.visibility).
#[must_use]
pub fn in_place_causes(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    index: u32,
) -> Vec<(Name, TextRange)> {
    let Some((key, summary)) = in_place_summary(db, program, file, index) else {
        return Vec::new();
    };
    let typed = &crate::infer_body(db, program, file, index).body;
    let names: Vec<Name> = typed
        .params
        .iter()
        .map(|(_, v)| typed.locals[v.0 as usize])
        .collect();
    let start = body_starts(db, program, file)[index as usize];
    causes(summary, key, in_place_params(db, program), &names)
        .into_iter()
        .map(|(name, at)| (name, at + start))
        .collect()
}
