//! Name resolution and declarations: each module's items, the module graph, `use`, and the names in
//! bodies (program.namespaces, declarations.name-lookup, traits.method-resolution), as queries of
//! the database.
//!
//! Resolution runs in steps, as the reference interpreter's does:
//!
//! 1. [`scope`]: each module gets a scope, of the items it declares and the names its `use`
//!    declarations bind, in a type namespace and a value namespace.
//! 2. [`lower`]: each module's header is checked against its name, and every declaration and
//!    body is resolved into its [`hir`] form, recording the places where one module names
//!    another.
//! 3. The places where modules name one another are checked for cycles.
//!
//! Then [`decls`] gathers what every item and impl block declares, and checks the impl blocks,
//! records and `main`, and the constants are checked for cycles. [`check`] reports all of their
//! diagnostics.
//!
//! Each step's results that later steps read hold no positions, so that an edit leaves them
//! unchanged unless it changes what they say, and the queries that read them don't run again.
//! Their diagnostics name the parts of items they are at, which the module's resolution places.
//!
//! Its place among the crates (`compiler/README.md`): it depends on `stilt-diag`, `stilt-syntax`
//! and `stilt-db`, and on no later phase: procedural macros run through the host that `stilt-
//! meta` installs ([`procs::install`]).

#![warn(missing_docs)]

mod consts;
mod cycles;
pub mod decls;
mod diagnostics;
pub mod exports;
pub mod foreign;
pub mod hir;
mod items;
pub mod lower;
pub mod macros;
pub mod procs;
pub mod scope;
pub mod values;

pub use crate::decls::{Declarations, declarations};
pub use crate::diagnostics::{FileDiagnostic, check, file_diagnostics};
pub use crate::items::{DeclSummary, ItemSummary, ItemTree, ValueParams, item_tree};
pub use crate::lower::{
    Input, ModuleResolution, body_at, body_starts, header_limits, module_body, module_hir,
    resolve_input, resolve_module,
};
pub use crate::scope::{DefMap, ModuleScope, def_map, module_scope};

/// A part of a module's items, where a diagnostic found without positions is reported.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Anchor {
    /// The start of the file.
    FileStart,
    /// The first token of the item at this index: its `use`, `impl`, `test` or `pub`, or the
    /// keyword that starts its declaration.
    Item(u32),
    /// The name of the item at this index.
    Name(u32),
    /// The name of a variant of the item at the first index, a type.
    Variant(u32, u32),
    /// The type of the item at this index, an impl block.
    ImplType(u32),
    /// The name of a member of the item at the first index, an impl block or trait.
    Member(u32, u32),
    /// The member type of the item at the first index, an impl block, that its `where`
    /// clause's bound at the second index bounds (traits.where).
    Where(u32, u32),
}

#[cfg(test)]
mod tests;
