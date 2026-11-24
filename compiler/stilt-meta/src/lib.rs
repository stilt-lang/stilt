//! The compile-time interpreter of Stilt's compiler, which runs procedural macros (macros.running
//! and macros.failed-uses) inside the compiler: never as a separate program, and never through the
//! code generator.
//!
//! A macro's run reads an [`image`] of the code it may reach, the typed bodies of its module
//! and of those it calls into, the standard library's among them, and [`eval`]uates them as the
//! reference interpreter does, counting steps, frames and memory as macros.step-limits counts them.
//! Its values ([`value`]) are those of the language and the natives of `std.meta` ([`meta`]).
//!
//! Its place among the crates (`compiler/README.md`): it depends on `stilt-syntax`, `stilt-db`,
//! `stilt-hir`, `stilt-types`, `stilt-mir` and `stilt-runtime`, and on no back end; name
//! resolution reaches it only through the host that [`install`] gives it.
#![warn(missing_docs)]

mod eval;
mod fiber;
mod frame;
mod host;
mod image;
mod limits;
mod meta;
mod natives;
mod run;
mod structural;
mod value;

/// Installs the host that runs procedural macros in this process, so that name resolution
/// expands their uses.
pub fn install() {
    stilt_hir::procs::install(Box::new(host::MetaHost));
}

#[cfg(test)]
mod tests;
