//! The host of procedural macros (macros.expansion-order, macros.running and macros.step-limits): a
//! macro's module is checked with the modules it imports, as a program of their own, and a macro of
//! it expands uses unless the module has an error. Each use's expansion is a query of its own,
//! keyed by the program of the macro's module and the use's tokens with spans relative to the use,
//! and the files they name, so that moving a use or editing another body runs no macro again
//! (reference/rationale/16-meta.md).

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::decls::{Lookup, QueriedOnce};
use stilt_hir::hir::{Input, Item, Name, result_form};
use stilt_hir::procs::{Call, Host, Outcome, Signature, State, closure};

/// The host that runs procedural macros in the compiler.
#[derive(Debug)]
pub(crate) struct MetaHost;

/// A use's run: the program of the macro's module, and the call.
#[salsa::interned(debug)]
pub(crate) struct Expansion<'db> {
    pub(crate) program: Program,
    #[returns(ref)]
    pub(crate) call: Call,
}

/// The run of a macro on a use, computed once for the same module and the same use.
#[salsa::tracked(returns(ref))]
pub(crate) fn expansion<'db>(db: &'db dyn Db, key: Expansion<'db>) -> Outcome {
    crate::run::run(db, *key.program(db), key.call(db))
}

/// The program of the module `home` of `program` and the modules it imports.
pub(crate) fn module_program(db: &dyn Db, program: Program, home: Name) -> Program {
    let mut files: Vec<SourceFile> = closure(db, program, home).clone();
    files.sort_by(|a, b| a.path(db).cmp(b.path(db)));
    let mut packages = program.packages(db).clone();
    for p in &mut packages.list {
        p.files.retain(|f| files.contains(f));
    }
    stilt_db::program_of(db, files, packages)
}

/// Whether the module `home` of `program` has an error, which keeps its macros from expanding
/// any use (macros.expansion-order).
fn has_error(db: &dyn Db, program: Program, home: Name) -> bool {
    let Some(file) = stilt_hir::def_map(db, program)
        .module(&home)
        .map(|m| m.file)
    else {
        return true;
    };
    stilt_types::check(db, program)
        .iter()
        .any(|d| d.file == file && d.diagnostic.is_error())
}

impl Host for MetaHost {
    fn state(&self, db: &dyn Db, program: Program, home: Name, name: Name) -> State {
        let sub = module_program(db, program, home);
        if has_error(db, sub, home) {
            return State::Unusable;
        }
        let item = Item { home, name };
        let decls = QueriedOnce::new(db, sub);
        let Some(sig) = decls.function(&item) else {
            return State::Unusable;
        };
        let inputs: Option<Vec<Input>> = sig.params.iter().map(|(_, t)| Input::of(t)).collect();
        match (inputs, result_form(&sig.ret)) {
            (Some(inputs), Some(result)) => State::Usable(Signature { inputs, result }),
            _ => State::Unusable,
        }
    }

    fn run<'db>(&self, db: &'db dyn Db, program: Program, call: Call) -> &'db Outcome {
        let sub = module_program(db, program, call.home);
        expansion(db, Expansion::new(db, sub, call))
    }
}
