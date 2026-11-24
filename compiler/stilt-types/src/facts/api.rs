//! The limitable facts of a package's API: the implicit effects of its items when verification
//! proves nothing (versions.limitable-facts; versions.facts-without-proofs).

use stilt_db::{Db, Program, SourceFile};

use super::Effect;
use crate::analyses::implicit;
use crate::queries::{body_count, body_owner, body_summary, module_info};

/// The implicit effects of the program's items and the standard library's when verification proves
/// nothing: the limitable facts of a package's API, which read no proof (versions.limitable-facts;
/// versions.facts-without-proofs). Only a package's API asks for them, so a check computes none.
#[salsa::tracked(returns(ref))]
fn unproved_effects(db: &dyn Db, program: Program) -> implicit::Effects {
    let mut summaries = Vec::new();
    for &file in program.std(db).iter().chain(program.files(db)) {
        for index in 0..body_count(db, program, file) {
            summaries.extend(body_summary(db, program, file, index).iter().cloned());
        }
    }
    implicit::unproved(&summaries)
}

/// The implicit effects that the item of the body `index` of `file` has when verification
/// proves nothing: `panic`, `overflow`, `alloc`, `div` and `locks`, then the capabilities. A
/// package's API reads them as its limitable facts, so a version's number follows no proof.
/// This crate infers no `copy`.
#[must_use]
pub fn api_effects(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> Vec<Effect> {
    let module = module_info(db, program, file);
    let Some(key) = body_owner(db, program, file, index).key(module.name) else {
        return Vec::new();
    };
    let effects = unproved_effects(db, program);
    (Effect::INFERRED.into_iter())
        .filter(|&e| effects.has(e, &key))
        .collect()
}
