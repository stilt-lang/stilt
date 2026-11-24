//! What a run's image takes from the database that holds its program: the program's code to start
//! it, then each edit's changed functions (goals edit-to-running-program and one-engine). `run`
//! lowers it from a database of its own when no engine holds the program, and the program's engine
//! lowers it the same way and sends it, so that the front end and the MIR run once, in the engine,
//! and `run` only compiles what it receives.

use std::collections::HashMap;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use stilt_db::{Database, Program};
use stilt_mir::mir::Function;
use stilt_mir::{CheckErrors, FnRef, Layouts, layouts};
use stilt_rc::{Counted, Reach};

/// What starting a run needs of its program.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct Start {
    /// The diagnostics of a program with errors, rendered as `check` renders them, which `run`
    /// reports first (program.programs-with-errors).
    pub(crate) diagnostics: String,
    /// The program's code, or why the program can't run.
    pub(crate) code: Result<Code, String>,
}

/// A program's code, as its image takes it.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct Code {
    /// Whether the program has errors, so that its run ends with status 2 however it ends.
    pub(crate) with_errors: bool,
    /// The paths of the program's files, by the indexes its locations use.
    pub(crate) files: Vec<String>,
    /// The functions its entry reaches, with their reference counting, those with an error
    /// replaced by panics.
    pub(crate) functions: Vec<Arc<Function>>,
    /// What each of them does about the check of `without alloc` (facts.without-alloc).
    pub(crate) guards: stilt_mir::Guards,
}

/// What an edit of the program's files changes in its run.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) enum Update {
    /// No file changed since the last look.
    Unchanged,
    /// The edited program has errors, so nothing is patched: its diagnostics, rendered.
    Errors(String),
    /// The edited program has no `main`, so nothing is patched.
    NoMain,
    /// The functions whose code the edit changed, and whether it changed the layout of the
    /// program's values, so that the program starts again, with the paths of its files.
    Patch {
        functions: Vec<Arc<Function>>,
        guards: stilt_mir::Guards,
        moved: bool,
        files: Vec<String>,
    },
    /// Why the program's files can't be read.
    Unreadable(String),
}

/// A run's program, as its image holds it. Each version is counted in a [`Counted`] that
/// several runs may share, as an engine's do, so that a run after another counts only what an
/// edit changed.
#[derive(Debug, Default)]
pub(crate) struct Lowering {
    /// What the program's entry reached in the version its image holds, so that an update
    /// walks again only what an edit changed.
    reach: Reach,
    /// The layouts of the program's values in the version its image holds.
    layouts: Option<Layouts>,
    /// The latest version of each function given to the image, so that an update gives it
    /// only the functions an edit changed.
    given: HashMap<FnRef, Arc<Function>>,
}

impl Lowering {
    /// What starting the program needs: its diagnostics if it has errors, and its code, in
    /// which the code with an error panics where it is reached (program.programs-with-errors).
    pub(crate) fn start(
        &mut self,
        db: &Database,
        program: Program,
        counted: &mut Counted,
    ) -> Start {
        let with_errors = has_errors(db, program);
        let (diagnostics, errors) = if with_errors {
            let report = crate::report::check(db, program, false);
            (report.stderr, crate::errors::check_errors(db, program))
        } else {
            (String::new(), CheckErrors::default())
        };
        if stilt_mir::code_of(db, program, main_fn()).is_none() {
            let code = Err("module `main` has no function `main`".to_owned());
            return Start { diagnostics, code };
        }
        let now = layouts(db, program);
        let files = files(db, program);
        // Nothing reads the database after the walk, which keeps it last, so that an engine's
        // edit, which cancels what reads it, never leaves a version half given.
        let functions = self.reach.update(db, program, roots(), &errors, counted);
        self.layouts = Some(now);
        let guards = stilt_mir::guards(db, program, &functions);
        let functions = self.give(functions);
        let code = Ok(Code {
            with_errors,
            files,
            functions,
            guards,
        });
        Start { diagnostics, code }
    }

    /// What the edited program changes in the run: nothing when it has errors or no `main`,
    /// and otherwise the functions whose code changed.
    pub(crate) fn update(
        &mut self,
        db: &Database,
        program: Program,
        counted: &mut Counted,
    ) -> Update {
        if has_errors(db, program) {
            return Update::Errors(crate::report::check(db, program, false).stderr);
        }
        if stilt_mir::code_of(db, program, main_fn()).is_none() {
            return Update::NoMain;
        }
        let now = layouts(db, program);
        let files = files(db, program);
        // As in `start`, nothing reads the database after the walk.
        let errors = CheckErrors::default();
        let functions = self.reach.update(db, program, roots(), &errors, counted);
        let moved = self.layouts.as_ref() != Some(&now);
        self.layouts = Some(now);
        let guards = stilt_mir::guards(db, program, &functions);
        Update::Patch {
            functions: self.give(functions),
            guards,
            moved,
            files,
        }
    }

    /// The functions that differ from those given before, which are given now. A function
    /// that didn't change is the same `Arc`, which tells it apart at no cost.
    fn give(&mut self, functions: Vec<Arc<Function>>) -> Vec<Arc<Function>> {
        functions
            .into_iter()
            .filter(|f| {
                let before = self.given.insert(f.name.clone(), Arc::clone(f));
                before.is_none_or(|g| !Arc::ptr_eq(&g, f) && *g != **f)
            })
            .collect()
    }
}

/// The roots of a run's walk: the program's entry.
fn roots() -> Vec<FnRef> {
    vec![FnRef::Main]
}

/// Whether the program has errors.
pub(crate) fn has_errors(db: &Database, program: Program) -> bool {
    stilt_rc::check_in_parallel(db, program)
        .iter()
        .any(|d| d.diagnostic.is_error())
}

/// The paths of the program's files, as its panics report them.
pub(crate) fn files(db: &Database, program: Program) -> Vec<String> {
    program
        .files(db)
        .iter()
        .map(|f| f.path(db).clone())
        .collect()
}

fn main_fn() -> FnRef {
    FnRef::Function(stilt_hir::hir::Item {
        home: "main".into(),
        name: "main".into(),
    })
}
