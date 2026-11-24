//! A program with errors runs all the same (program.programs-with-errors): every function, method
//! or constant whose body has an error is replaced by a panic of kind `check-error`
//! (effects.panic-kinds), raised as soon as it is called or read, and so is every method that a
//! trait impl lacks.
//!
//! The bodies without errors meet no error type, so their lowering never meets one. Should one
//! do so all the same, the function panics in the same way, at its own name.

use std::collections::HashMap;
use std::sync::Arc;

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::hir::Item;

use crate::items::{Code, code_of};
use crate::lower::Cx;
use crate::lower::functions::check_error;
use crate::mir::{Block, Const, Function, Operand, Terminator};
use crate::{FnRef, functions};

/// The runtime's number of the panic kind `check-error` (effects.panic-kinds).
const CHECK_ERROR: u64 = 9;

/// Where a `check-error` panic is reported, and its detail.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckError {
    /// The location, as the runtime packs it: the name of the function, method or constant,
    /// or the `impl` keyword of an impl that lacks the method.
    pub loc: u64,
    /// The panic's detail.
    pub detail: Arc<str>,
}

/// The code of a program that panics in place of running.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CheckErrors {
    /// The panic of each body with an error, by its file and index.
    pub bodies: HashMap<(SourceFile, u32), CheckError>,
    /// The panic of each method that a trait impl lacks, by the impl's trait and type
    /// constructor.
    pub missing: HashMap<(Item, Item), CheckError>,
    /// The place of each body of the program's files, where a function whose lowering meets
    /// the error type all the same panics.
    pub names: HashMap<(SourceFile, u32), u64>,
    /// Whether the program has errors.
    pub any: bool,
}

impl CheckErrors {
    /// Whether the program has no error at all.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        !self.any
    }

    /// The functions that make up `f`: its own and its closures', or a panic in their place.
    pub(crate) fn functions(&self, db: &dyn Db, program: Program, f: &FnRef) -> Vec<Arc<Function>> {
        let lowered = functions(db, program, f.clone()).clone();
        if self.is_empty() {
            return lowered;
        }
        let cx = Cx { db, program };
        let code = code_of(db, program, f.clone());
        let replaced = |error: &CheckError| {
            check_error(&cx, f, error)
                .into_iter()
                .map(Arc::new)
                .collect()
        };
        if let Some(Code::Body(file, index)) = code
            && let Some(error) = self.bodies.get(&(file, index))
        {
            return replaced(error);
        }
        if lowered.is_empty() {
            if let FnRef::ImplMethod(trait_item, owner, _) = f
                && let Some(error) = self.missing.get(&(trait_item.clone(), owner.clone()))
            {
                return replaced(error);
            }
            return lowered;
        }
        let at = match code {
            Some(Code::Body(file, index)) => self.names.get(&(file, index)).copied(),
            _ => None,
        };
        let error = CheckError {
            loc: at.unwrap_or(0),
            detail: "".into(),
        };
        lowered
            .into_iter()
            .map(|g| {
                if g.broken {
                    Arc::new(panicking((*g).clone(), &error))
                } else {
                    g
                }
            })
            .collect()
    }
}

/// The panic that stands for code with an error.
pub(crate) fn panic_terminator(error: &CheckError) -> Terminator {
    let detail =
        (!error.detail.is_empty()).then(|| Operand::Const(Const::Str(error.detail.clone())));
    Terminator::Panic {
        kind: CHECK_ERROR,
        detail,
        loc: Operand::word(error.loc),
    }
}

/// A function that keeps its parameters but panics as soon as it is called.
fn panicking(mut g: Function, error: &CheckError) -> Function {
    g.blocks = vec![Block {
        stmts: Vec::new(),
        term: panic_terminator(error),
    }];
    g.broken = false;
    g
}
