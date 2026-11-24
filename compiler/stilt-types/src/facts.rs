//! The implicit effects of each function with the operations of its body that cause them,
//! which `stilt show` prints (facts.visibility; goal shown-facts). They are read from the
//! queries that the limits of `without` read: the implicit effects of the program, and the
//! operations of the function's typed body. So are the types that inference gives the
//! variables a body binds, which `show` writes in (Inferred facts, "Seven commands"), and the
//! views of each function and whether its module names a view type (views.std-view and views.show),
//! the operations that may share values between threads (par.atomic-sites), and the `unsafe`
//! blocks and foreign functions of each body (c.unsafe-and-foreign).

mod api;
mod atomic;
mod effects;
mod parameters;
mod polymorphism;
mod shapes;
mod unsafe_code;
mod views;

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::body_starts;
use stilt_hir::decls::QueriedOnce;
use stilt_hir::hir::GenericId;
use stilt_syntax::TextRange;

use crate::analyses::implicit;
pub use crate::analyses::implicit::Effect;
use crate::queries::{body_owner, generic_name, implicit_effects, infer_body, module_info, scope};
use crate::tast::walk::{iter, iter_block};
use crate::tast::{Code, Definition, Stmt, StmtKind};
use crate::ty::Table;
pub use api::api_effects;
pub use atomic::atomic_causes;
pub use parameters::uses_parameters;
pub use polymorphism::uses_polymorphism;
pub use shapes::writes_shapes;
pub use unsafe_code::{foreign_uses, unsafe_blocks};
pub use views::{Viewing, names_views, tier, views};

/// Whether a span of a body lies in one of its macro uses, which the user wrote (macros.expansion).
fn in_expansion(expansions: &[stilt_hir::hir::Expansion], at: stilt_syntax::TextRange) -> bool {
    expansions
        .iter()
        .any(|e| e.parent.is_none() && e.at.contains_range(at))
}

/// An operation of a function's body that gives the function an implicit effect.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cause {
    /// The effect it gives.
    pub effect: Effect,
    /// Where the operation is in its file.
    pub at: TextRange,
    /// What the operation does, as the errors of the limits say it, such as "an index can
    /// panic" or "`digits` allocates, through `List.new`".
    pub says: String,
}

/// The operations of the body `index` of a file's module that give its function an implicit
/// effect, in the order of the body, once for each effect each gives (facts.inference). A body
/// that isn't a function's has none, and so has one with an error, which has no implicit effect
/// (facts.bodies-with-errors).
#[must_use]
pub fn effect_causes(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> Vec<Cause> {
    let module = module_info(db, program, file);
    let Some(key) = body_owner(db, program, file, index).key(module.name) else {
        return Vec::new();
    };
    let decls = QueriedOnce::new(db, program);
    let scope = scope(db, program, file, index, Some(&key));
    let Some(sites) = implicit::code_sites(&decls, &scope) else {
        return Vec::new();
    };
    let start = body_starts(db, program, file)[index as usize];
    implicit::causes(
        module.name,
        Some(&key),
        implicit_effects(db, program),
        &sites,
    )
    .into_iter()
    .map(|(effect, at, says)| Cause {
        effect,
        at: at + start,
        says,
    })
    .collect()
}

/// A check of a function's body that a rule of acceptance proves can't fail, where a `panic`
/// would otherwise have been, with the rule (facts.shown-proofs).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proved {
    /// Where the operation is in its file.
    pub at: TextRange,
    /// What it can't fail of.
    pub check: crate::verify::Check,
    /// The rule that proves it.
    pub rule: crate::accept::Rule,
}

/// The checks of the body `index` of a file's module that a rule of acceptance proves, in the
/// order of the body, each where `show` prints `proved bounds by a range loop` and the others:
/// a body that isn't a function's, or has an error, has none.
#[must_use]
pub fn proved_checks(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> Vec<Proved> {
    let module = module_info(db, program, file);
    let Some(key) = body_owner(db, program, file, index).key(module.name) else {
        return Vec::new();
    };
    let decls = QueriedOnce::new(db, program);
    let scope = scope(db, program, file, index, Some(&key));
    let Some(sites) = implicit::code_sites(&decls, &scope) else {
        return Vec::new();
    };
    let start = body_starts(db, program, file)[index as usize];
    sites
        .iter()
        .filter_map(|s| {
            let (check, rule) = s.proved().filter(|(c, _)| c.shown().is_some())?;
            Some(Proved {
                at: s.at() + start,
                check,
                rule,
            })
        })
        .collect()
}

/// A pattern that a `let` or a `var` binds, with the type that inference gives it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bound {
    /// Where the pattern is in its file.
    pub at: TextRange,
    /// Its type, as a program writes it.
    pub ty: String,
}

/// The patterns of the `let` and `var` statements of the body `index` of a file's module, those
/// of its closures included, in the order they are written, each with the type that inference
/// gives it (types.inferred-per-body). A body with an error has none.
#[must_use]
pub fn local_types(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> Vec<Bound> {
    let Definition::Code(code) = &infer_body(db, program, file, index).body.code else {
        return Vec::new();
    };
    let start = body_starts(db, program, file)[index as usize];
    let names = |id: &GenericId| *generic_name(db, program, id.clone());
    let table = Table::default();
    let mut found = Vec::new();
    // A binding that a macro's template writes is no code of the user's (macros.showing).
    let expansions = &stilt_hir::module_body(db, program, file, index).expansions;
    let mut stmt = |s: &Stmt| {
        if let StmtKind::Let(b) | StmtKind::Var(b) = &s.kind
            && !expansions.iter().any(|e| e.at == b.pattern.at)
        {
            found.push(Bound {
                at: b.pattern.at + start,
                ty: table.show(&b.pattern.ty, &names),
            });
        }
    };
    match code {
        Code::Block(b) => iter_block(b, &mut stmt, &mut |_| {}),
        Code::Expr(e) => iter(e, &mut stmt, &mut |_| {}),
    }
    found
}
