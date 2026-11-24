//! The MIR of Stilt's compiler: each function of a program as a control-flow graph over
//! word-sized locals, lowered from the typed bodies of `stilt-types` (Compiler architecture).
//!
//! A value is the words of its type's layout ([`layout`]): one for a scalar or a heap word, and
//! one per word for a record, a tuple or a variant whose type isn't recursive, which is held
//! inline, in locals, fields and lists. Generic code is compiled for the layouts of its type
//! arguments ([`Held`]), and takes a witness for each type parameter, its argument's
//! [`shape`], and a dictionary for each bound, so it holds a value of a type
//! parameter in the words that the code that names its type holds it in. A raise is an
//! ordinary return, flagged, so there is no unwinding (effects.raise). Reference counting is added
//! afterwards, by `stilt-rc`, from the ownership that [`mir`] defines.
//!
//! Its place among the crates (`compiler/README.md`): it depends on `stilt-diag`, `stilt-syntax`,
//! `stilt-db`, `stilt-hir` and `stilt-types`, and on no later phase or back end.

#![warn(missing_docs)]

mod build;
mod cases;
pub mod check_errors;
pub mod described;
pub mod floats;
mod guards;
pub mod items;
mod layout;
mod lower;
pub mod mir;
pub mod opt;
pub mod print;
pub mod profiling;
mod prune;
mod repr;
pub mod shape;
pub mod special;
mod synth;
mod walk;

use std::collections::HashMap;
use std::sync::Arc;

use stilt_db::{Db, Program};
use stilt_hir::decls::{TraitInfo, TypeInfo};
use stilt_hir::hir::Item;

pub use cases::{TestBody, std_tests, tests};
pub use check_errors::{CheckError, CheckErrors};
pub use guards::{Guard, Guards, guards, key_of};
pub use items::{
    Code, Cross, FnRef, Foreign, Held, ImplRef, Known, Shape, Word, bodies, code_of, native_bodies,
};
pub use lower::strings::spec_words;
pub use opt::inline::user::{Named, inline_calls};
pub use opt::inline::{inline_reached, inlined};
pub use print::print;
pub use stilt_hir::exports::{CType, Export};
pub use synth::input::{Input, layouts_of, lower_input};
pub use synth::props::{Property, property};
pub use walk::{Reached, Renewed, Walk, Walked, reached, reached_from, referenced};

use crate::lower::Cx;
use crate::mir::Function;

/// The functions that make up `f`: its own, and those of the closures it holds. A native function
/// has none. These are the functions that a build reaches, kept so that a build after an edit
/// lowers again only the functions the edit changed (goal edit-to-running-program).
// Salsa takes a query's key by value.
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked(returns(ref))]
pub fn functions(db: &dyn Db, program: Program, f: FnRef) -> Vec<Arc<Function>> {
    lowered(db, program, &f)
        .into_iter()
        .map(|g| Arc::new(g.fitted()))
        .collect()
}

/// The functions that make up `f`, which [`functions`] keeps.
fn lowered(db: &dyn Db, program: Program, f: &FnRef) -> Vec<Function> {
    let cx = Cx { db, program };
    synth::synthesize(&cx, f).unwrap_or_else(|| lower::lower(&cx, f))
}

/// The entry, then every function and constant whose body is in one of the program's own files, in
/// the order of their names: the roots of a program whose every function may run, as a patched
/// program's may.
#[salsa::tracked(returns(ref))]
pub fn every_function(db: &dyn Db, program: Program) -> Vec<FnRef> {
    let files = program.files(db);
    let mut all: Vec<FnRef> = bodies(db, program)
        .code
        .iter()
        .filter(|(f, code)| {
            !matches!(f, FnRef::Test(..))
                && matches!(code, Code::Body(file, _) if files.contains(file))
        })
        .map(|(f, _)| f.clone())
        .collect();
    all.sort_by_cached_key(FnRef::symbol);
    all.insert(0, FnRef::Main);
    all
}

/// What the layout of a program's values follows: its types' declarations, and its traits', which
/// its dictionaries follow. A value made before a change to them has no meaning after it, so a
/// running program whose layouts change starts again.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layouts {
    types: HashMap<Item, TypeInfo>,
    traits: HashMap<Item, TraitInfo>,
}

/// The layouts of a program's values.
#[must_use]
pub fn layouts(db: &dyn Db, program: Program) -> Layouts {
    let decls = stilt_hir::declarations(db, program);
    Layouts {
        types: decls.types.clone(),
        traits: decls.traits.clone(),
    }
}
