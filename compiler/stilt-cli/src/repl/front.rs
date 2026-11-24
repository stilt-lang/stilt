//! The database's side of a REPL session (repl.scope, repl.inputs, repl.input-checking,
//! repl.answers, repl.running-inputs, repl.program-edits and repl.bindings-across-edits): the
//! session's module, the types of its bindings, and what its inputs name of the program, followed
//! from one version of the program to the next as `run` follows a running program. It answers each
//! of the session's asks with what the session's image must load and run. It lives in the REPL's
//! process, or in the program's engine, so that the front end and the MIR run there (goal
//! one-engine).
//!
//! Each answer first takes in the program as it is now: its diagnostics, when they changed and
//! hold an error; the bindings whose types an edit changed, which the session drops; and the
//! functions that the inputs reach whose code changed, which the image patches. Reading the
//! database comes first and changing the front last, so that an engine's edit, which cancels
//! what reads the database, never leaves the front half changed.

use std::collections::HashMap;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use stilt_db::{Database, Program};
use stilt_hir::hir::Name;
use stilt_mir::mir::Function;
use stilt_mir::{CheckErrors, FnRef, Layouts};
use stilt_rc::{Counted, Reach};

use super::bindings::Binding;
use super::input::{Compiled, Source, compile};

/// What a session asks of its program, with the ids of the bindings it holds: those that the
/// inputs that ran made, and no other, so that the front forgets those of an input that a raise
/// or a panic ended.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct Ask {
    pub(crate) live: Vec<u32>,
    pub(crate) what: Asked,
}

/// What a session asks.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) enum Asked {
    /// To compile an input.
    Input { text: String, number: u32 },
    /// To check inputs in another module, `:module NAME`.
    Module(String),
}

/// What a session's image does on an answer.
#[derive(Debug, Default, Serialize, Deserialize)]
pub(crate) struct Answer {
    /// What to write to stderr first: the program's diagnostics, the notes of the bindings
    /// dropped, and the input's diagnostics or why it was refused.
    pub(crate) report: String,
    /// The bindings to drop.
    pub(crate) dropped: Vec<u32>,
    /// The paths of the program's files, by the indexes its locations use, when they changed.
    pub(crate) files: Option<Vec<String>>,
    /// The functions to load: those the edits changed, and the input's.
    pub(crate) functions: Vec<Arc<Function>>,
    /// The input to run, if there is one.
    pub(crate) run: Option<Run>,
}

/// An input to run.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct Run {
    pub(crate) entry: FnRef,
    /// The bindings that its parameters take, in order, whose words make its frame.
    pub(crate) params: Vec<u32>,
    /// The type of an expression's value, as a program writes it; `None` for a `let`.
    pub(crate) ty: Option<String>,
    /// The bindings that a `let` makes, in order.
    pub(crate) binds: Vec<Bind>,
}

/// A binding that a `let` makes: its id, its name, its type and the heapness of its words.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct Bind {
    pub(crate) id: u32,
    pub(crate) name: String,
    pub(crate) ty: String,
    pub(crate) heap: Vec<bool>,
}

/// The database's side of a session.
#[derive(Debug)]
pub(crate) struct Front {
    /// The module whose scope inputs are checked in.
    module: Name,
    bindings: Vec<Binding>,
    /// The id of the next binding.
    next: u32,
    /// What the inputs name of the program.
    roots: Vec<FnRef>,
    reach: Reach,
    /// The latest version of each function given to the image.
    given: HashMap<FnRef, Arc<Function>>,
    layouts: Layouts,
    /// The paths of the program's files, as the image last had them.
    files: Vec<String>,
    /// The program's diagnostics when they were last reported, if they held an error.
    reported: String,
}

/// A front's answer, before the front takes in what it changes.
struct Prepared {
    answer: Answer,
    bindings: Vec<Binding>,
    module: Option<Name>,
    roots: Vec<FnRef>,
    layouts: Layouts,
    reported: String,
}

impl Front {
    /// The front of a session on `program`, with what the session reports first, the program's
    /// diagnostics if it has errors, and the paths of its files.
    pub(crate) fn open(db: &Database, program: Program) -> (Self, String, Vec<String>) {
        let reported = errors(db, program);
        let files = crate::run::files(db, program);
        let front = Self {
            module: Name::from("main"),
            bindings: Vec::new(),
            next: 0,
            roots: Vec::new(),
            reach: Reach::default(),
            given: HashMap::new(),
            layouts: stilt_mir::layouts(db, program),
            files: files.clone(),
            reported: reported.clone(),
        };
        (front, reported, files)
    }

    /// The answer to `ask`, on the program as it is now, whose functions are counted in
    /// `counted`.
    pub(crate) fn ask(
        &mut self,
        db: &Database,
        program: Program,
        counted: &mut Counted,
        ask: &Ask,
    ) -> Answer {
        let prepared = self.prepare(db, program, counted, ask);
        self.commit(prepared)
    }

    /// The answer to `ask`, and what it changes in the front, which is taken in once nothing
    /// reads the database any more. Only the walk of what the inputs reach changes before,
    /// which an update keeps only once it is done.
    fn prepare(
        &mut self,
        db: &Database,
        program: Program,
        counted: &mut Counted,
        ask: &Ask,
    ) -> Prepared {
        let mut p = self.edited(db, program, &ask.live);
        match &ask.what {
            Asked::Module(name) => {
                if stilt_hir::def_map(db, program).is_module(name) {
                    p.module = Some(Name::from(name.as_str()));
                } else {
                    let refusal = format!("stilt: the program has no module `{name}`\n");
                    p.answer.report += &refusal;
                }
            }
            Asked::Input { text, number } => {
                let source = Source {
                    text,
                    number: *number,
                };
                match self.input(db, program, &p.bindings, source, counted) {
                    Ok(compiled) => self.compiled(db, program, compiled, &mut p),
                    Err(report) => p.answer.report += &report,
                }
            }
        }
        if !p.roots.is_empty() {
            let errors = if crate::run::has_errors(db, program) {
                crate::errors::check_errors(db, program)
            } else {
                CheckErrors::default()
            };
            let reached = self
                .reach
                .update(db, program, p.roots.clone(), &errors, counted);
            p.answer.functions.splice(0..0, reached);
        }
        p
    }

    /// Takes in what an answer changes, and gives the answer, with only the functions that
    /// differ from those the image was given.
    fn commit(&mut self, p: Prepared) -> Answer {
        let mut answer = p.answer;
        if let Some(module) = p.module {
            self.module = module;
        }
        if let Some(files) = &answer.files {
            self.files.clone_from(files);
        }
        self.next = (p.bindings.iter().map(|b| b.id + 1))
            .max()
            .unwrap_or(0)
            .max(self.next);
        self.bindings = p.bindings;
        self.roots = p.roots;
        self.layouts = p.layouts;
        self.reported = p.reported;
        answer.functions.retain(|f| {
            let before = self.given.insert(f.name.clone(), Arc::clone(f));
            before.is_none_or(|g| !Arc::ptr_eq(&g, f) && *g != **f)
        });
        answer
    }

    /// The program as it is now: its diagnostics if they changed and hold an error, the paths
    /// of its files if they changed, and the bindings among `live` whose types an edit changed,
    /// dropped.
    fn edited(&self, db: &Database, program: Program, live: &[u32]) -> Prepared {
        let mut answer = Answer::default();
        let reported = errors(db, program);
        if reported != self.reported {
            answer.report += &reported;
        }
        let files = crate::run::files(db, program);
        if files != self.files {
            answer.files = Some(files);
        }
        let layouts = stilt_mir::layouts(db, program);
        let moved = layouts != self.layouts;
        let mut bindings = self.bindings.clone();
        bindings.retain(|b| live.contains(&b.id));
        bindings.retain(|b| {
            let kept = b.unchanged(db, program, moved);
            if !kept {
                answer.dropped.push(b.id);
                answer.report += &b.note();
            }
            kept
        });
        Prepared {
            answer,
            bindings,
            module: None,
            roots: self.roots.clone(),
            layouts,
            reported,
        }
    }

    /// Compiles an input in the session's module, with `bindings`.
    fn input(
        &self,
        db: &Database,
        program: Program,
        bindings: &[Binding],
        source: Source<'_>,
        counted: &mut Counted,
    ) -> Result<Compiled, String> {
        let map = stilt_hir::def_map(db, program);
        let Some(module) = map.module(&self.module) else {
            return Err(format!(
                "stilt: the program has no module `{}` any more: `:module NAME` names another\n",
                self.module
            ));
        };
        let params: Vec<_> = bindings.iter().map(|b| (b.name, b.ty.clone())).collect();
        compile(db, program, module.file, &params, source, counted)
    }

    /// Takes in a compiled input: its functions, what they name and the bindings it makes,
    /// which a binding of the same name keeps company until the session tells whether the
    /// input ran, and so replaced it.
    fn compiled(&self, db: &Database, program: Program, compiled: Compiled, p: &mut Prepared) {
        p.answer.report += &compiled.warnings;
        let params = p.bindings.iter().map(|b| b.id).collect();
        for root in compiled.roots {
            if !p.roots.contains(&root) {
                p.roots.push(root);
            }
        }
        let mut binds = Vec::new();
        for (id, (name, ty, heap)) in (self.next..).zip(compiled.bound) {
            let binding = Binding::new(db, program, id, name, ty);
            binds.push(Bind {
                id,
                name: binding.name.to_string(),
                ty: binding.shown.clone(),
                heap,
            });
            p.bindings.push(binding);
        }
        let entry = (compiled.functions.iter())
            .find(|f| matches!(f.name, FnRef::InputEntry(_)))
            .map(|f| f.name.clone());
        let ty = compiled
            .ty
            .map(|t| stilt_types::input::shown(db, program, &t));
        p.answer.functions = compiled.functions;
        p.answer.run = entry.map(|entry| Run {
            entry,
            params,
            ty,
            binds,
        });
    }
}

/// The program's diagnostics, rendered as `check` renders them, if it has errors, and otherwise
/// nothing.
fn errors(db: &Database, program: Program) -> String {
    if crate::run::has_errors(db, program) {
        crate::report::check(db, program, false).stderr
    } else {
        String::new()
    }
}
