//! What translating a function asks of its registry, which a build that reuses the function's
//! machine code asks again ([`crate::reuse`]).
//!
//! Translation declares the data and the imports that a function names as it first meets them,
//! so the numbers and names of the module's symbols follow the order in which the functions ask
//! for them. A build that reuses a function's code asks again what its translation asked, in its
//! order and where the translation would have, so that every symbol is declared under the number
//! and the name that translating every function gives it, and the object is the same byte for
//! byte. It checks each answer that the code depends on too: whether a callee is compiled, that a
//! slot exists, and the cells of the constants that the entry releases. Each number in the code
//! is the answer to one question, so the answer to it asked again is the number that the code
//! takes in this build.

use std::collections::HashSet;
use std::sync::Arc;

use cranelift_codegen::ir::Signature;
use cranelift_module::{DataId, FuncId, Module};
use rustc_hash::{FxBuildHasher, FxHashMap as HashMap};
use stilt_mir::FnRef;
use stilt_mir::mir::{Const, Function, Repr};

use super::Registry;

/// The conventions of each function that a module compiles, each the positions of the
/// parameters it owns.
pub(crate) type Known = HashMap<FnRef, Vec<Vec<usize>>>;

/// One thing that translation asked of a registry.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Asked {
    /// The static object of a constant string or data object, declared when first asked.
    Data(Const),
    /// A function of the runtime, imported when first asked.
    Import(String, Signature),
    /// A foreign function, imported when first asked (c.build-targets).
    Foreign(String, Signature),
    /// The cell of a constant's value, of these words, declared when first asked.
    Constant(FnRef, Box<[Repr]>),
    /// The runtime's stop flag, imported when first asked.
    Stop,
    /// Whether a function is compiled, with the answer.
    Compiled(FnRef, bool),
    /// The slot of a function in the convention that owns these parameters, which exists.
    Slot(FnRef, Vec<usize>),
    /// The cells of the constants declared so far, which the entry releases.
    Constants(Vec<(FnRef, Box<[Repr]>)>),
    /// The guard of a function for the check of `without alloc`, with the answer.
    Guard(FnRef, Option<stilt_mir::Guard>),
}

/// The number that a question gave, if it gives one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Answer {
    None,
    Function(FuncId),
    Data(DataId),
}

/// The conventions of each of `functions`, which drafts read: those that declaring each of them
/// gives it a slot in ([`Registry::declare`]).
pub(crate) fn known(functions: &[Arc<Function>]) -> Arc<Known> {
    let mut known = Known::with_capacity_and_hasher(functions.len(), FxBuildHasher);
    for f in functions {
        let owned = super::owned_params(f);
        let conventions: &mut Vec<Vec<usize>> = known.entry(f.name.clone()).or_default();
        if !conventions.contains(&owned) {
            conventions.push(owned);
        }
    }
    Arc::new(known)
}

impl Registry {
    /// A registry that translates a function apart, into a draft of the module
    /// ([`crate::draft`]): it knows the functions that the module compiles, `known`, and
    /// numbers on its own what it declares, so that the translation asks what translating the
    /// function into the module asks, and gets numbers of its own.
    pub(crate) fn draft(&self, known: &Arc<Known>) -> Self {
        let mut draft = Self::new(HashSet::new());
        draft.available = Arc::clone(&self.available);
        draft.known = Some(Arc::clone(known));
        (draft.watched, draft.object, draft.debug) = (self.watched, self.object, self.debug);
        draft.guards = Arc::clone(&self.guards);
        draft
    }

    /// Asks again what a function's translation asked, in its order, declaring what it
    /// declared, and gives each answer when every answer that the code depends on is the one
    /// the translation had: `None` at the first that isn't, when the function has to be
    /// translated again.
    pub(crate) fn ask_again<'a>(
        &mut self,
        module: &mut dyn Module,
        asked: impl ExactSizeIterator<Item = &'a Asked>,
    ) -> Result<Option<Vec<Answer>>, String> {
        let mut answers = Vec::with_capacity(asked.len());
        for a in asked {
            let answer = match a {
                Asked::Data(c) => Answer::Data(self.data(module, c)?),
                Asked::Import(name, sig) => Answer::Function(self.import(module, name, sig)?),
                Asked::Foreign(name, sig) => Answer::Function(self.foreign(module, name, sig)?),
                Asked::Constant(f, words) => Answer::Data(self.constant(module, f, words)?),
                Asked::Stop => Answer::Data(self.stop_flag(module)?),
                Asked::Compiled(f, compiled) if self.compiled(f) == *compiled => Answer::None,
                Asked::Guard(f, guard) if self.guard(f) == *guard => Answer::None,
                Asked::Slot(f, owned) => match self.slot(module, f, owned) {
                    Ok(id) => Answer::Data(id),
                    Err(_) => return Ok(None),
                },
                Asked::Constants(cells)
                    if self.constants.len() == cells.len()
                        && (self.constants.iter().zip(cells))
                            .all(|((f, _, words), (g, kept))| f == g && words == kept) =>
                {
                    Answer::None
                }
                Asked::Compiled(..) | Asked::Constants(_) | Asked::Guard(..) => return Ok(None),
            };
            answers.push(answer);
        }
        Ok(Some(answers))
    }
}
