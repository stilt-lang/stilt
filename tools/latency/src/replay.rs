//! Replaying an edit script against a warm query database: each edit's time from the file's
//! change to the program's diagnostics, the bodies it type checks again, and whether its
//! diagnostics are a clean check's. The clean checks run once the replay is done, so that none
//! shares the machine with an edit being timed, and several at once, each in a database and on
//! a thread of its own, since nothing else runs then.

use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::thread;
use std::time::Duration;

use salsa::{Database as _, DatabaseKeyIndex, Durability, EventKind, Setter as _, Storage};
use stilt_db::{Db, Program, SourceFile};
use stilt_diag::Diagnostic;
use stilt_hir::FileDiagnostic;

use crate::clock::Clock;
use crate::script::{Edit, Kind};
use crate::split::Split;

/// A database that records the queries it runs, which tells the bodies an edit checks again (goal
/// body-edits-recheck-one-body). Salsa calls it back at each query it reads, which slows proving
/// its memos unchanged, so only the replay that counts what runs holds its program in one.
#[salsa::db]
#[derive(Clone)]
pub(crate) struct Recording {
    storage: Storage<Self>,
    ran: Arc<Mutex<Vec<DatabaseKeyIndex>>>,
    extras: stilt_db::Extras,
}

impl Recording {
    pub(crate) fn new() -> Self {
        let ran = Arc::new(Mutex::new(Vec::new()));
        let recorded = Arc::clone(&ran);
        Self {
            storage: Storage::new(Some(Box::new(move |event| {
                if let EventKind::WillExecute { database_key } = event.kind {
                    recorded
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push(database_key);
                }
            }))),
            ran,
            extras: stilt_db::Extras::default(),
        }
    }

    /// A new revision in which nothing changed, so that the next query proves every memo it
    /// reads unchanged, as after an edit, but runs none of them again.
    pub(crate) fn nothing_changed(&mut self) {
        self.synthetic_write(Durability::LOW);
    }

    /// How many times the query `name` ran since this was last asked.
    pub(crate) fn runs_of(&self, name: &str) -> usize {
        let ran = std::mem::take(&mut *self.ran.lock().unwrap_or_else(PoisonError::into_inner));
        salsa::attach(self, || {
            ran.iter()
                .filter(|key| format!("{key:?}").split('(').next() == Some(name))
                .count()
        })
    }
}

#[salsa::db]
impl salsa::Database for Recording {}

#[salsa::db]
impl Db for Recording {
    fn extras(&self) -> &stilt_db::Extras {
        &self.extras
    }
}

/// A project: its files' paths, the names their places give their modules, and their texts.
#[derive(Clone)]
pub(crate) struct Project {
    pub(crate) paths: Vec<String>,
    pub(crate) modules: Vec<Vec<String>>,
    pub(crate) texts: Vec<String>,
}

impl Project {
    /// The project at `root`, as `stilt check` loads it.
    pub(crate) fn load(root: &Path) -> Result<Self, String> {
        let db = stilt_db::Database::default();
        let program = stilt_db::load(&db, root)?;
        let files = program.files(&db);
        Ok(Self {
            paths: files.iter().map(|f| f.path(&db).clone()).collect(),
            modules: files.iter().map(|f| f.module_path(&db).clone()).collect(),
            texts: files
                .iter()
                .map(|f| String::from_utf8_lossy(f.bytes(&db)).into_owned())
                .collect(),
        })
    }

    pub(crate) fn program(&self, db: &dyn Db) -> (Program, Vec<SourceFile>) {
        let files: Vec<SourceFile> = self
            .paths
            .iter()
            .zip(&self.modules)
            .zip(&self.texts)
            .map(|((path, module), text)| {
                stilt_db::source_file(db, path.clone(), module.clone(), text.as_bytes().to_vec())
            })
            .collect();
        (stilt_db::program(db, files.clone()), files)
    }
}

/// A program's diagnostics, with the paths of their files.
type Diagnostics = Vec<(String, Diagnostic)>;

/// The program's diagnostics, as `stilt check` finds them: its bodies checked in parallel.
fn diagnostics<D: Db + Clone>(db: &D, program: Program) -> Diagnostics {
    shown(db, stilt_types::check_in_parallel(db, program))
}

fn shown(db: &dyn Db, found: &[FileDiagnostic]) -> Diagnostics {
    found
        .iter()
        .map(|d| (d.file.path(db).clone(), d.diagnostic.clone()))
        .collect()
}

/// The diagnostics of the project's current texts, checked from scratch, each body in order,
/// and how long that took: a check that shares neither memos nor threads with the replay's.
pub(crate) fn clean(project: &Project) -> (Diagnostics, Duration) {
    let db = stilt_db::Database::default();
    let (program, _) = project.program(&db);
    let start = Clock::own();
    let found = shown(&db, stilt_types::check(&db, program));
    (found, start.elapsed())
}

/// What one edit cost.
#[derive(Clone, Debug)]
pub(crate) struct Step {
    pub(crate) kind: Kind,
    pub(crate) time: Duration,
    /// How many bodies were type checked again.
    pub(crate) inferred: usize,
    /// Whether its diagnostics differ from a clean check's (goal incremental-equals-clean), when
    /// that was compared.
    pub(crate) differs: bool,
    /// How many diagnostics the program has after it.
    pub(crate) diagnostics: usize,
    pub(crate) split: Split,
}

/// Replays `edits` on `project`, comparing each step with a clean check when `compare`.
pub(crate) fn replay(project: &mut Project, edits: &[Edit], compare: bool) -> Vec<Step> {
    let mut db = Recording::new();
    let (program, files) = project.program(&db);
    diagnostics(&db, program);
    db.runs_of("infer_body");
    let mut steps = Vec::new();
    // Each step's texts and diagnostics, which a clean check compares once the replay is done.
    let mut compared = Vec::new();
    for edit in edits {
        project.texts[edit.file].clone_from(&edit.text);
        let start = Clock::own();
        files[edit.file]
            .set_bytes(&mut db)
            .to(edit.text.as_bytes().to_vec());
        let found = diagnostics(&db, program);
        let time = start.elapsed();
        let inferred = db.runs_of("infer_body");
        db.nothing_changed();
        let start = Clock::own();
        diagnostics(&db, program);
        let split = Split::front_end(time, start.elapsed());
        steps.push(Step {
            kind: edit.kind,
            time,
            inferred,
            differs: false,
            diagnostics: found.len(),
            split,
        });
        if compare {
            compared.push((project.texts.clone(), found));
        }
    }
    for (step, differs) in steps.iter_mut().zip(differ(project, &compared)) {
        step.differs = differs;
    }
    steps
}

/// The stack of each thread of clean checks, as large as the compiler gives the threads that
/// check bodies, since checking recurses as deep as an expression is nested.
const STACK: usize = 16 * 1024 * 1024;

/// How many clean checks run at once: each database holds the whole project, about 600 MB for
/// the 50K-line one.
const AT_ONCE: usize = 4;

/// Whether the diagnostics of each step differ from a clean check of its texts, the checks run
/// [`AT_ONCE`] at a time, each in order in a database of its own.
fn differ(project: &Project, compared: &[(Vec<String>, Diagnostics)]) -> Vec<bool> {
    let threads = thread::available_parallelism()
        .map_or(1, usize::from)
        .min(AT_ONCE);
    let next = AtomicUsize::new(0);
    let mut differs = vec![false; compared.len()];
    thread::scope(|scope| {
        let workers: Vec<_> = (0..threads.min(compared.len()))
            .map(|_| {
                let next = &next;
                thread::Builder::new()
                    .stack_size(STACK)
                    .spawn_scoped(scope, move || {
                        let mut done = Vec::new();
                        loop {
                            let i = next.fetch_add(1, Ordering::Relaxed);
                            let Some((texts, found)) = compared.get(i) else {
                                return done;
                            };
                            let mut step = project.clone();
                            step.texts.clone_from(texts);
                            done.push((i, clean(&step).0 != *found));
                        }
                    })
                    .expect("a thread for clean checks")
            })
            .collect();
        for worker in workers {
            let done = worker
                .join()
                .unwrap_or_else(|e| std::panic::resume_unwind(e));
            for (i, d) in done {
                differs[i] = d;
            }
        }
    });
    differs
}
