//! What a body's owner says about how its body is checked.

use crate::infer::BodyKind;
use crate::owners::{BodyOwner, Place};

use super::ModuleInfo;

/// How a body is checked, by what it is the code of.
pub(super) fn body_kind(owner: &BodyOwner) -> BodyKind<'_> {
    match owner {
        BodyOwner::Fn {
            signature,
            hole: false,
            ..
        } => BodyKind::Fn(signature),
        BodyOwner::Fn {
            signature,
            hole: true,
            ..
        } => BodyKind::Hole(signature),
        BodyOwner::Const(ty, _) => BodyKind::Const(ty),
        BodyOwner::Test => BodyKind::Test,
        BodyOwner::Example => BodyKind::Example,
    }
}

/// Whether the body is the program's `main`'s (program.main).
pub(super) fn is_main(module: &ModuleInfo, owner: &BodyOwner) -> bool {
    !module.std
        && &*module.name == "main"
        && matches!(owner, BodyOwner::Fn { name, place: Place::Module, .. } if &**name == "main")
}

/// Whether fixes may edit the signature of a body's function: a trait's method signatures bind
/// those of its default methods and of its impls' methods (traits.declaring-trait and
/// traits.implementing-trait).
pub(super) fn owns_signature(owner: &BodyOwner) -> bool {
    matches!(
        owner,
        BodyOwner::Fn {
            place: Place::Module
                | Place::Impl {
                    trait_item: None,
                    ..
                },
            ..
        }
    )
}

/// Whether the body is a procedural macro's (macros.procedural-bodies), whose errors are raised, not
/// named in a row.
pub(super) fn is_procedural(owner: &BodyOwner) -> bool {
    matches!(
        owner,
        BodyOwner::Fn {
            procedural: true,
            ..
        }
    )
}
