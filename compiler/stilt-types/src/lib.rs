//! Type checking, and the analyses that follow it (errors.phases; errors.registry-phases).
//!
//! Each body is checked on its own against the signatures of the declarations, with inference
//! local to the body, and elaborated into a [`tast::TypedBody`]: [`infer_body`]. A body is a
//! function, a test, a doc example or a constant's value. The later phases read the typed
//! bodies: [`body_diagnostics`] gives a body's diagnostics of every phase, and [`check`] those
//! of a whole program, which [`check_in_parallel`] checks across the machine's cores, and
//! [`facts::effect_causes`] the operations that give a function its implicit effects, and
//! [`promises`] what the checks of `copy` read of them.
//!
//! Its place among the crates (`compiler/README.md`): it depends on `stilt-diag`, `stilt-syntax`,
//! `stilt-pkg`, `stilt-db` and `stilt-hir`, and on no phase after type checking.

#![warn(missing_docs)]

pub mod accept;
mod analyses;
mod copies;
mod cow;
pub mod cycles;
pub mod facts;
pub mod generable;
pub mod holes;
mod implements;
mod infer;
pub mod input;
mod literal;
mod meets;
mod owners;
pub mod packages;
mod parallel;
pub mod params;
pub mod position;
pub mod promises;
mod queries;
pub mod reflects;
pub mod tast;
pub mod ty;
mod unify;
pub mod verify;

pub use accept::accepted;
pub use analyses::implicit::alloc::is_recursive;
pub use cow::Cow;
pub use implements::{Bounds, implements_trait};
pub use meets::{hir_holds_error, meets_error_type, signature_holds_error};
pub use parallel::check_in_parallel;
pub use queries::{Inference, body_diagnostics, check, generic_name, infer_body, keep_typed};
pub use unify::Problem;
pub use verify::{released, verified};

pub(crate) use stilt_syntax::TextRange;

#[cfg(test)]
mod tests;
