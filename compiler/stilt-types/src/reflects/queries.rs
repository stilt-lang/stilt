//! The queries of reflection's facts (meta.reflects and meta.types-without-shape): one summary of
//! each body, the fixed point of the program's, each function's facts, the traits of descriptors'
//! tables, and E0350 in a body.

#![expect(
    clippy::drop_non_drop,
    reason = "salsa's macro drops each query's key, which an item's interned names leave with \
              nothing to free"
)]

use stilt_db::{Db, Program, SourceFile};
use stilt_diag::Diagnostic;
use stilt_hir::decls::QueriedOnce;
use stilt_hir::hir::{GenericId, Item};

use super::Key;

use crate::queries::{body_count, body_owner, generic_name, infer_body, module_info};
use crate::tast::{Code, Definition};

/// What the facts of reflection read of the body `index`, if it is a function's (meta.reflects and
/// meta.types-without-shape).
#[salsa::tracked(returns(ref))]
pub(crate) fn reflect_summary(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    index: u32,
) -> Option<super::Summary> {
    let module = module_info(db, program, file);
    let key = body_owner(db, program, file, index).key(module.name)?;
    let Definition::Code(Code::Block(block)) = &infer_body(db, program, file, index).body.code
    else {
        return None;
    };
    let decls = QueriedOnce::new(db, program);
    Some(super::summary(&decls, key, block))
}

/// The facts of reflection of the program's functions and the standard library's (meta.reflects).
#[salsa::tracked(returns(ref))]
pub(crate) fn reflections(db: &dyn Db, program: Program) -> super::Reflections {
    let mut summaries = Vec::new();
    for &file in program.std(db).iter().chain(program.files(db)) {
        for index in 0..body_count(db, program, file) {
            summaries.extend(reflect_summary(db, program, file, index).iter().cloned());
        }
    }
    super::solve(&summaries)
}

/// The facts of reflection of one function: each of its type parameters whose descriptor a
/// debug build passes it, and whether it reflects on it (meta.reflects). A query of
/// its own, so that what reads one function's facts reads nothing again when another's change.
// A query's arguments are its key, which salsa takes by value.
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked(returns(ref))]
pub fn reflects(db: &dyn Db, program: Program, key: super::Key) -> Vec<super::Fact> {
    reflections(db, program).of(&key).to_vec()
}

/// The traits whose impls a descriptor's table holds, in order: `Eq` and
/// `Hash`, by which a set's and a map's `make` keep the first of equal elements, the traits
/// that the bound tests of the program and of the standard library name, and those by which
/// their impls bound their type parameters, so that the table of a type built from a type
/// parameter's descriptor finds the impls that the parameter's own table holds.
#[salsa::tracked(returns(ref))]
pub fn tested_traits(db: &dyn Db, program: Program) -> Vec<Item> {
    let mut traits: Vec<Item> = ["Eq", "Hash"].map(stilt_hir::decls::prelude_item).to_vec();
    for &file in program.std(db).iter().chain(program.files(db)) {
        for index in 0..body_count(db, program, file) {
            for (_, t) in reflect_summary(db, program, file, index)
                .iter()
                .flat_map(|s| &s.guards)
            {
                if !traits.contains(t) {
                    traits.push(t.clone());
                }
            }
        }
    }
    let decls = stilt_hir::declarations(db, program);
    let mut i = 0;
    while i < traits.len() {
        let mut impls: Vec<_> = decls
            .trait_impls
            .iter()
            .filter(|((t, _), _)| *t == traits[i])
            .collect();
        impls.sort_by(|a, b| a.0.cmp(b.0));
        for t in impls
            .into_iter()
            .flat_map(|(_, info)| info.generics.iter().flat_map(|(_, b)| b))
        {
            if !traits.contains(t) {
                traits.push(t.clone());
            }
        }
        i += 1;
    }
    traits
}

/// E0350 in the body `index` (meta.types-without-shape), from the facts of the functions it uses.
pub(crate) fn reflect_errors(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    index: u32,
) -> Vec<Diagnostic> {
    let Some(s) = reflect_summary(db, program, file, index) else {
        return Vec::new();
    };
    if s.uses.is_empty() && s.shapes.is_empty() {
        return Vec::new();
    }
    let mut keys: Vec<super::Key> = s.uses.iter().map(|u| u.callee.clone()).collect();
    keys.push(s.key.clone());
    keys.sort();
    keys.dedup();
    let facts = keys
        .into_iter()
        .map(|k| (k.clone(), reflects(db, program, k).clone()))
        .collect();
    let facts = super::Reflections::of_functions(facts);
    let decls = QueriedOnce::new(db, program);
    let generics = |id: &GenericId| *generic_name(db, program, id.clone());
    let module = module_info(db, program, file);
    let names = super::Names {
        generics: &generics,
        module: &module.name,
    };
    super::errors(&decls, &names, s, &facts)
}

/// The names of the type parameters a function reflects on, in the order it declares them, as
/// `stilt show` prints `reflects T` beside its signature (meta.reflects).
#[must_use]
pub fn reflected(db: &dyn Db, program: Program, key: super::Key) -> Vec<String> {
    let mut found: Vec<GenericId> = reflects(db, program, key)
        .iter()
        .filter(|f| f.reflects.is_some())
        .map(|f| f.param.clone())
        .collect();
    found.sort_by_key(|g| g.index);
    found
        .into_iter()
        .map(|g| {
            if g == super::self_param() {
                "Self".to_owned()
            } else {
                generic_name(db, program, g).to_string()
            }
        })
        .collect()
}

/// The type parameters whose descriptors a debug build passes beside their witnesses, as a
/// dictionary is passed: a trait method's own that its default or an impl's
/// method reads, the matching ones of every impl's method, and a trait's parameters that a
/// default reads; and the traits whose defaults read `Self`'s.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Carried {
    generics: Vec<GenericId>,
    selves: Vec<Item>,
}

impl Carried {
    /// Whether a type parameter's descriptor travels with its witness.
    #[must_use]
    pub fn generic(&self, g: &GenericId) -> bool {
        self.generics.binary_search(g).is_ok()
    }

    /// Whether the default methods of trait `t` take `Self`'s descriptor.
    #[must_use]
    pub fn self_of(&self, t: &Item) -> bool {
        self.selves.contains(t)
    }
}

/// The type parameters whose descriptors travel with their witnesses ([`Carried`]).
#[salsa::tracked(returns(ref))]
pub fn carried(db: &dyn Db, program: Program) -> Carried {
    let facts = reflections(db, program);
    let mut out = Carried::default();
    for (key, read) in facts.all() {
        let Key::DefaultMethod(t, _) = key else {
            continue;
        };
        for f in read {
            if f.param == super::self_param() {
                out.selves.push(t.clone());
            } else {
                out.generics.push(f.param.clone());
            }
        }
    }
    out.generics.sort();
    out.generics.dedup();
    out.selves.sort();
    out.selves.dedup();
    let lookup = QueriedOnce::new(db, program);
    let decls = stilt_hir::declarations(db, program);
    let mut own = Vec::new();
    for ((t, owner), info) in &decls.trait_impls {
        for m in &info.members {
            let key = Key::ImplMethod(t.clone(), owner.clone(), m.name);
            for (a, b) in super::bounds::own_of_trait(&lookup, &key) {
                if out.generic(&b) {
                    own.push(a);
                }
            }
        }
    }
    out.generics.extend(own);
    out.generics.sort();
    out.generics.dedup();
    out
}
