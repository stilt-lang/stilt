//! The program after name resolution (program.namespaces, declarations.name-lookup).
//!
//! The tree follows the syntax, except that every name refers to what it names:
//! - a name in an expression is a local variable, an item, or a member of a type or trait;
//! - a name in a type is an item or a generic, and `Self` inside an impl block is the block's
//!   type;
//! - a name in a pattern is a variable, a variant, a constant or a record type.
//!
//! A name that fails to resolve becomes an error node, which the type checker gives the error
//! type (errors.error-type). Fields and methods of values stay fields, for the type checker, which
//! needs the receiver's type.
//!
//! Declarations hold no positions, so that an edit that moves code changes none of them, and
//! the queries that read only declarations don't run again. Bodies hold the positions of their
//! parts, for their diagnostics.

mod body;
mod decls;
mod effects;
mod expansions;
mod name;
mod names;
mod patterns;
mod quotes;
mod rebase;
mod records;
pub mod walk;

pub(crate) use rebase::{rebase, remap_diagnostic, remap_expr, remap_pat};

pub use body::*;
pub use decls::*;
pub use effects::*;
pub use expansions::*;
pub use names::*;
pub use patterns::*;
pub use quotes::*;
pub use records::*;
pub use stilt_syntax::ast::{Limit, Mode};

/// Gives a vector no more room than it holds, in a block of its own: the database keeps every
/// body's tree, and a vector grown by pushes, or collected from an iterator of unknown length,
/// holds up to four times what it needs (goal bounded-cache). Shrinking in place could leave
/// the allocator's block as it was.
pub fn fit<T>(v: &mut Vec<T>) {
    if v.capacity() > v.len() {
        let mut exact = Vec::with_capacity(v.len());
        exact.append(v);
        *v = exact;
    }
}
