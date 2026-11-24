//! The queries of type checking and of the later phases.
//!
//! A body's queries read only what checking it needs: its own HIR, with positions relative to
//! its start, what its declaration says, its module's header, and each declaration it names,
//! one at a time. So an edit inside a body checks only that body again, and an edit of a signature
//! only the bodies that read it (goals edit-to-diagnostics and body-edits-recheck-one-body).

#![expect(
    clippy::drop_non_drop,
    reason = "salsa's macro drops each query's key, which interned names may leave with nothing \
              to free"
)]

mod owned;
mod text;

use stilt_db::{Db, Program, SourceFile};
use stilt_diag::Diagnostic;
use stilt_hir::decls::{Lookup, QueriedOnce};
use stilt_hir::hir::{BodyIndex, GenericId, Item, Limits, Name};
use stilt_hir::{FileDiagnostic, body_starts, def_map, header_limits, module_body, module_hir};

use crate::analyses::implicit::in_place::{self, InPlace};
use crate::analyses::implicit::{self, Key};
use crate::analyses::{self, SigInfo, unsafe_limit};
use crate::infer::{Env, check_body};
use crate::owners::{BodyOwner, Place, generic_name as declared_name, owner_of};
use crate::tast::{Code, Definition, TypedBody};
use crate::ty::Ty;
use owned::{body_kind, is_main, is_procedural, owns_signature};

/// A body after type checking, with its type errors. Their positions are relative to the
/// body's start.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Inference {
    /// The typed body.
    pub body: TypedBody,
    /// Its type errors, in the order found.
    pub diagnostics: Vec<Diagnostic>,
}

/// What checking a module's bodies needs of its header and `use` declarations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ModuleInfo {
    pub(crate) name: Name,
    pub(crate) std: bool,
    /// The edition its package is read with; the standard library's is the first
    /// (editions.renames).
    pub(crate) edition: &'static str,
    /// What the header's `without` limits (program.header-limits).
    limits: Limits,
    pub(crate) imports: Vec<Name>,
}

#[salsa::tracked(returns(ref))]
pub(crate) fn module_info(db: &dyn Db, program: Program, file: SourceFile) -> ModuleInfo {
    let m = module_hir(db, program, file);
    let packages = &program.packages(db).list;
    let edition = match packages.get(stilt_db::package_of(db, program, file)) {
        Some(p) if !m.std => p.edition,
        _ => stilt_pkg::edition::first().name,
    };
    ModuleInfo {
        name: m.name,
        std: m.std,
        edition,
        limits: m.limits,
        imports: m.imports.clone(),
    }
}

/// What the body `index` of a file's module is the code of.
#[salsa::tracked(returns(ref))]
pub(crate) fn body_owner(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> BodyOwner {
    owner_of(module_hir(db, program, file), BodyIndex(index))
}

/// The name of a type parameter or row variable, for messages.
// A query's arguments are its key, which salsa takes by value.
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked(returns(ref))]
pub fn generic_name(db: &dyn Db, program: Program, id: GenericId) -> Name {
    if let Some(letter) = id.fresh_letter() {
        return Name::from(letter.to_string());
    }
    def_map(db, program)
        .modules
        .iter()
        .find(|m| m.name == id.owner.decl.module)
        .and_then(|m| declared_name(module_hir(db, program, m.file), &id))
        .unwrap_or_else(|| Name::from("_"))
}

/// The traits visible to method calls in a module (traits.traits-in-scope): the prelude's, the
/// module's own, and those of the modules it imports.
pub(crate) fn visible_traits(decls: &dyn Lookup, module: &ModuleInfo) -> Vec<Item> {
    let mut traits = decls.module_traits("std.prelude").to_vec();
    if &*module.name != "std.prelude" {
        traits.extend_from_slice(decls.module_traits(&module.name));
    }
    for import in &module.imports {
        traits.extend_from_slice(decls.module_traits(import));
    }
    traits
}

/// Type checks the body `index` of a file's module, on its own against the signatures of the
/// declarations (errors.phases). It reads the signatures of what it calls, never their bodies.
/// An engine forgets it once a build has lowered what it needs ([`keep_typed`]).
#[salsa::tracked(returns(ref), lru = 0)]
pub fn infer_body(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> Inference {
    let body = module_body(db, program, file, index);
    let module = module_info(db, program, file);
    let owner = body_owner(db, program, file, index);
    let decls = QueriedOnce::new(db, program);
    let names = |id: &GenericId| *generic_name(db, program, id.clone());
    let renames = stilt_pkg::edition::renames(module.edition);
    let (bounds, self_ty) = match owner {
        // A trait's default method, or constant, is checked where `Self` is a type that
        // implements the trait (traits.trait-constants).
        BodyOwner::Fn {
            place: Place::Trait(t),
            ..
        }
        | BodyOwner::Const(_, Some(t)) => (vec![(Ty::SelfTy, vec![t.clone()])], Some(Ty::SelfTy)),
        _ => (Vec::new(), None),
    };
    // Within its trait, `Self` gives the trait's parameters themselves (traits.member-types).
    let bound_args = bounds
        .iter()
        .flat_map(|(rigid, traits)| traits.iter().map(move |t| (rigid.clone(), t.clone())))
        .filter_map(|(rigid, t)| {
            let info = decls.trait_info(&t)?;
            let params = info
                .params
                .iter()
                .cloned()
                .map(Ty::Param)
                .collect::<Vec<_>>();
            (!params.is_empty()).then_some((rigid, t, params))
        })
        .collect();
    let env = Env {
        decls: &decls,
        module: module.name,
        std: module.std,
        traits: visible_traits(&decls, module),
        bounds,
        bound_args,
        self_ty,
        names: &names,
        imports: &module.imports,
        signature: body.signature.as_ref().filter(|_| owns_signature(owner)),
        main: is_main(module, owner),
        procedural: is_procedural(owner),
        renames: &renames,
    };
    let (body, diagnostics) = check_body(env, body, body_kind(owner), module.std);
    debug_assert!(
        !module.std || diagnostics.is_empty(),
        "the standard library has errors: {diagnostics:?}"
    );
    Inference { body, diagnostics }
}

/// Keeps the typed bodies of only the `n` bodies read last, from the next revision on, or every
/// one when `n` is 0, as a database does unless told otherwise. Once a build has lowered the
/// functions it reaches, only an edit, or a command that reads a body's types, needs a typed
/// body again (goal bounded-cache).
pub fn keep_typed(db: &mut dyn Db, n: usize) {
    infer_body::set_lru_capacity(db, n);
}

/// Whether the body `index` of a file's module has an error that keeps the later phases from
/// it: the result of [`infer_body`] that checking a program in parallel reads, so that checking
/// it again proves each body checked without reading its typed body, which an engine may have
/// forgotten (goal bounded-cache).
#[salsa::tracked]
pub(crate) fn broken(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> bool {
    matches!(
        infer_body(db, program, file, index).body.code,
        Definition::Broken
    )
}

/// What limits a function's body: its module's header, and its own `without`.
pub(crate) fn body_limits(module: &ModuleInfo, owner: &BodyOwner) -> Limits {
    match owner {
        BodyOwner::Fn { limits, .. } => module.limits.or(*limits),
        BodyOwner::Const(..) | BodyOwner::Test | BodyOwner::Example => Limits::default(),
    }
}

/// What finding the sites of the body `index` needs of its function (facts.own-storage,
/// facts.in-place-parameters and facts.copy-at-call).
pub(crate) fn scope<'a>(
    db: &'a dyn Db,
    program: Program,
    file: SourceFile,
    index: u32,
    key: Option<&'a Key>,
) -> implicit::Scope<'a> {
    scope_with(
        db,
        program,
        (file, index),
        key,
        in_place_params(db, program),
    )
}

/// What finding the sites of the body `index` needs, with the in-place parameters `in_place`.
fn scope_with<'a>(
    db: &'a dyn Db,
    program: Program,
    (file, index): (SourceFile, u32),
    key: Option<&'a Key>,
    in_place: &'a InPlace,
) -> implicit::Scope<'a> {
    let module = module_info(db, program, file);
    implicit::Scope {
        module: &module.name,
        key,
        limits: body_limits(module, body_owner(db, program, file, index)),
        body: &infer_body(db, program, file, index).body,
        in_place,
        accepted: crate::accept::accepted(db, program, file, index),
    }
}

/// The summary of the body `index`, if it is a function's that the analysis counts: what the
/// implicit effects of the program need of one body (facts.inference).
#[salsa::tracked(returns(ref))]
pub(crate) fn body_summary(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    index: u32,
) -> Option<implicit::Summary> {
    let module = module_info(db, program, file);
    let key = body_owner(db, program, file, index).key(module.name)?;
    let scope = scope(db, program, file, index, Some(&key));
    implicit::summary(&QueriedOnce::new(db, program), &scope, key.clone())
}

/// What the in-place parameters of the program need of the body `index`, if it is a function's that
/// `without alloc` limits (facts.in-place-parameters). It reads no other body's facts, so the fixed
/// point over the call graph reads it.
#[salsa::tracked(returns(ref))]
pub(crate) fn in_place_summary(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    index: u32,
) -> Option<(Key, in_place::Summary)> {
    let module = module_info(db, program, file);
    let owner = body_owner(db, program, file, index);
    let key = owner.key(module.name)?;
    if !body_limits(module, owner).alloc {
        return None;
    }
    // The summary reads no in-place parameter, so the fixed point reads it without a cycle.
    let no_facts = InPlace::new();
    let scope = scope_with(db, program, (file, index), Some(&key), &no_facts);
    let found = in_place::summary(&QueriedOnce::new(db, program), &scope);
    Some((key, found))
}

/// The in-place parameters of the program's functions and the standard library's
/// (facts.in-place-parameters), which callers copy their arguments for (facts.copy-at-call).
#[salsa::tracked(returns(ref))]
pub fn in_place_params(db: &dyn Db, program: Program) -> InPlace {
    let mut summaries = Vec::new();
    for &file in program.std(db).iter().chain(program.files(db)) {
        for index in 0..body_count(db, program, file) {
            summaries.extend(in_place_summary(db, program, file, index).iter().cloned());
        }
    }
    in_place::solve(&summaries)
}

/// Whether the body `index` is a function's that a `without` limits, whose diagnostics then
/// read the implicit effects of the whole program.
pub(crate) fn reads_effects(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> bool {
    let owner = body_owner(db, program, file, index);
    let limits = body_limits(module_info(db, program, file), owner);
    matches!(owner, BodyOwner::Fn { .. }) && limits.any()
}

pub(crate) fn body_count(db: &dyn Db, program: Program, file: SourceFile) -> u32 {
    u32::try_from(body_starts(db, program, file).len()).expect("under 4G bodies")
}

/// The items of the program and the standard library that can panic and those that allocate
/// (facts.inference). A function that a `without` limits counts as one without the effect it
/// rules out, since its own operations are errors where they are written (effects.without-panic;
/// facts.without).
#[salsa::tracked(returns(ref))]
pub(crate) fn implicit_effects(db: &dyn Db, program: Program) -> implicit::Effects {
    let mut summaries = Vec::new();
    for &file in program.std(db).iter().chain(program.files(db)) {
        for index in 0..body_count(db, program, file) {
            summaries.extend(body_summary(db, program, file, index).iter().cloned());
        }
    }
    summaries.extend(implicit::foreign_summaries(db, program));
    implicit::effects(&summaries)
}

/// The items that a `without alloc` limits and those that allocate, which the check of debug
/// builds reads (facts.without-alloc): none of either when no item is limited, so that a program
/// without the limit is compiled as it would be without the check.
#[salsa::tracked(returns(ref))]
pub(crate) fn alloc_guards(db: &dyn Db, program: Program) -> crate::promises::AllocGuards {
    // The limits are read from the declarations, so that a program without one computes no
    // body's facts, which only the check needs.
    let mut limited = std::collections::BTreeSet::new();
    for &file in program.std(db).iter().chain(program.files(db)) {
        let module = module_info(db, program, file);
        for index in 0..body_count(db, program, file) {
            let owner = body_owner(db, program, file, index);
            if body_limits(module, owner).alloc
                && let Some(key) = owner.key(module.name)
            {
                limited.insert(key);
            }
        }
    }
    if limited.is_empty() {
        return crate::promises::AllocGuards::default();
    }
    let allocating = implicit_effects(db, program)
        .alloc
        .keys()
        .cloned()
        .collect();
    crate::promises::AllocGuards {
        limited,
        allocating,
    }
}

/// The diagnostics of the body `index` of a program's file: its type errors, and then those of
/// the later phases (errors.phases). Their positions are relative to the body's start, but
/// for the notes that show a macro's template.
#[salsa::tracked(returns(ref))]
pub fn body_diagnostics(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    index: u32,
) -> Vec<Diagnostic> {
    let inference = infer_body(db, program, file, index);
    let mut found = inference.diagnostics.clone();
    let module = module_info(db, program, file);
    let owner = body_owner(db, program, file, index);
    // The later phases check functions, tests and doc examples, not constants' values.
    let checked = match owner {
        BodyOwner::Fn { .. } => owner.key(module.name).is_some(),
        BodyOwner::Test | BodyOwner::Example => true,
        BodyOwner::Const(..) => false,
    };
    if let (true, Definition::Code(Code::Block(block))) = (checked, &inference.body.code) {
        let body: &TypedBody = &inference.body;
        let names = |id: &GenericId| *generic_name(db, program, id.clone());
        let decls = QueriedOnce::new(db, program);
        let hir = module_body(db, program, file, index);
        let text = || text::body_text(db, program, file, index);
        let line = |at| text::line_of(db, program, file, index, at);
        let sig = SigInfo {
            names: &names,
            params: hir
                .params
                .iter()
                .map(|v| {
                    let local = &hir.locals[v.0 as usize];
                    (local.name, local.at)
                })
                .collect(),
            spans: hir.signature.as_ref().filter(|_| owns_signature(owner)),
            module: &module.name,
            imports: &module.imports,
            raise_broken: matches!(owner, BodyOwner::Fn { signature, .. }
                if matches!(signature.row.raise.as_deref(), Some(stilt_hir::hir::Ty::Error))),
            text: &text,
            line: &line,
            block_end: hir.signature.as_ref().map(|s| s.end),
            projection: matches!(owner, BodyOwner::Fn { signature, .. } if signature.projection),
            analysed: &hir.analysed,
        };
        let key = owner.key(module.name);
        let limited = limited(db, program, (file, index), key.as_ref());
        // The sites, and the proofs they read (facts.verification), only where a limit, a `when` or
        // a call of `Lazy.new` checks them.
        let when = implicit::locks::checks(block);
        let scope =
            (limited.is_some() || when).then(|| scope(db, program, file, index, key.as_ref()));
        let limits = limited.as_ref().zip(scope.as_ref());
        let effects = when.then(|| implicit_effects(db, program));
        let held = effects.zip(scope.as_ref());
        let reflected = crate::reflects::queries::reflect_errors(db, program, file, index);
        let later = analyses::check(&decls, &sig, body, block, limits, held, reflected);
        let header = header_limits(db, program, file);
        found.extend(unsafe_limit::with_errors(later, owner, header, hir));
    }
    // An error at a macro's use that its template's own tokens put there names the macro and
    // shows the template (macros.errors-in-expansions).
    let expansions = &module_body(db, program, file, index).expansions;
    if expansions.is_empty() {
        return found;
    }
    found
        .into_iter()
        .map(|d| stilt_hir::hir::noted(expansions, d))
        .collect()
}

/// What limits the body `index`, if a `without` limits its function, whose item is `key`.
fn limited<'a>(
    db: &'a dyn Db,
    program: Program,
    (file, index): (SourceFile, u32),
    key: Option<&'a Key>,
) -> Option<implicit::Limited<'a>> {
    let module = module_info(db, program, file);
    let owner = body_owner(db, program, file, index);
    let BodyOwner::Fn {
        name, signature, ..
    } = owner
    else {
        return None;
    };
    body_limits(module, owner).any().then(|| implicit::Limited {
        module: &module.name,
        function: name,
        key,
        header: header_limits(db, program, file),
        own: &module_body(db, program, file, index).limits,
        raises_str: signature
            .row
            .raise
            .as_deref()
            .is_some_and(|e| Ty::from_hir(e, None) == Ty::str()),
        effects: implicit_effects(db, program),
    })
}

/// The diagnostics of a program: the syntax errors of its parts, those of its manifests, of its
/// names and declarations, of type checking and of the later phases, and its warnings, its
/// duplicate bodies among them (docs.duplicate-bodies), but for those that a part with a syntax
/// error holds back (errors.part-reports) and those of its fetched packages
/// (packages.dependencies-with-errors). They are sorted by file, position and code, and their fixes
/// are tidied against their files.
#[salsa::tracked(returns(ref))]
pub fn check(db: &dyn Db, program: Program) -> Vec<FileDiagnostic> {
    let mut all = stilt_hir::check(db, program).clone();
    let files = stilt_db::reported_files(db, program);
    all.extend(crate::packages::diagnostics(db, program).iter().cloned());
    for &file in files {
        let syntax = stilt_db::syntax_errors(db, file);
        let starts = body_starts(db, program, file);
        for index in 0..body_count(db, program, file) {
            let start = starts[index as usize];
            all.extend(
                body_diagnostics(db, program, file, index)
                    .iter()
                    .map(|d| d.clone().shifted(start))
                    .filter(|d| !syntax.holds_back(d))
                    .map(|diagnostic| FileDiagnostic { file, diagnostic }),
            );
        }
    }
    all.extend(
        crate::copies::warnings(db, program, files)
            .into_iter()
            .filter(|d| !stilt_db::syntax_errors(db, d.file).holds_back(&d.diagnostic)),
    );
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
    for d in all.iter_mut().filter(|d| !d.diagnostic.fixes.is_empty()) {
        if let Ok(text) = std::str::from_utf8(d.file.bytes(db)) {
            d.diagnostic = d.diagnostic.clone().tidied(text);
        }
    }
    all
}
