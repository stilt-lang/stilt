//! Replaying an edit script against a program held in an image, as `stilt run` holds it: each
//! edit's time from the file's change until the program's new code is live, every call of an edited
//! function then running it (goal edit-to-running-program), and whether the image then holds the
//! code that walking and counting the program afresh gives it (incremental-equals-clean).
//!
//! The image holds every function of the project, not only those its entry reaches, since an
//! edit may change any of them. An edit that leaves the program with errors patches nothing,
//! and one that changes the layout of its values restarts it, which costs no compilation more.
//! The program is held in a database that records no query, as `run`'s is, since a database
//! that records them is called back at each query it reads.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;

use salsa::{Durability, Setter as _};
use stilt_codegen_clif::Image;
use stilt_db::{Database, Program};
use stilt_mir::mir::Function;
use stilt_mir::{CheckErrors, FnRef, Layouts, every_function, layouts, reached_from};
use stilt_rc::{Counted, Reach};

use crate::clock::Clock;
use crate::replay::Project;
use crate::script::{Edit, Kind};
use crate::split::Split;

/// What one edit cost the running program.
#[derive(Clone, Debug)]
pub(crate) struct HotStep {
    pub(crate) kind: Kind,
    /// From the file's change until the new code is live, or until the diagnostics are ready
    /// when the edit leaves errors.
    pub(crate) time: Duration,
    /// How many functions were compiled again.
    pub(crate) compiled: usize,
    /// Whether the program starts again, its layouts changed.
    pub(crate) restarts: bool,
    /// Whether the edit leaves the program with errors, so that nothing is patched.
    pub(crate) errors: bool,
    /// Whether the image then holds other code for a function the program reaches than walking and
    /// counting the program afresh gives it (goal incremental-equals-clean).
    pub(crate) differs: bool,
    pub(crate) split: Split,
}

/// What one update of the image did, and what it cost after the front end.
struct Update {
    compiled: usize,
    restarts: bool,
    codegen: Duration,
    patching: Duration,
}

/// A program held in an image, with what it needs to take the next version.
struct Held {
    image: Image,
    reach: Reach,
    counted: Counted,
    layouts: Layouts,
    /// The latest code given to the image of each function.
    given: HashMap<FnRef, Arc<Function>>,
}

impl Held {
    fn new(db: &Database, program: Program) -> Result<Self, String> {
        let mut held = Self {
            image: Image::new()?,
            reach: Reach::default(),
            counted: Counted::default(),
            layouts: layouts(db, program),
            given: HashMap::new(),
        };
        held.update(db, program)?;
        Ok(held)
    }

    /// The program's functions with their reference counting that may differ from those the
    /// image holds, as `run` finds them.
    fn counted(&mut self, db: &Database, program: Program) -> Vec<Arc<Function>> {
        let roots = every_function(db, program).clone();
        let errors = CheckErrors::default();
        self.reach
            .update(db, program, roots, &errors, &mut self.counted)
    }

    /// Compiles the program's changed functions into the image, and tells how many there
    /// were, whether the layouts changed, and what that cost.
    fn update(&mut self, db: &Database, program: Program) -> Result<Update, String> {
        let start = Clock::own();
        let functions = self.counted(db, program);
        let loaded = self.image.load(&functions)?;
        let codegen = start.elapsed().saturating_sub(loaded.patching);
        for f in functions {
            self.given.insert(f.name.clone(), f);
        }
        let start = Clock::own();
        let now = layouts(db, program);
        let restarts = now != self.layouts;
        self.layouts = now;
        Ok(Update {
            compiled: loaded.compiled.len(),
            restarts,
            codegen,
            patching: loaded.patching + start.elapsed(),
        })
    }

    /// Whether the image holds other code for a function the program reaches than walking the
    /// program afresh and counting each function it reaches gives it (goal
    /// incremental-equals-clean).
    fn differs(&mut self, db: &Database, program: Program) -> bool {
        let roots = every_function(db, program).clone();
        let fresh = reached_from(db, program, &roots, &CheckErrors::default()).functions;
        let counted = self.counted.insert(db, program, fresh);
        counted.iter().any(|f| {
            self.given
                .get(&f.name)
                .is_none_or(|g| !Arc::ptr_eq(g, f) && **g != **f)
        })
    }
}

/// Replays `edits` on `project` held in an image, after timing the image's first load: a
/// clean check and a clean build of every function.
pub(crate) fn replay_hot(
    project: &mut Project,
    edits: &[Edit],
) -> Result<(Duration, Vec<HotStep>), String> {
    let mut db = Database::default();
    let (program, files) = project.program(&db);
    let start = Clock::own();
    if has_errors(&db, program) {
        return Err(
            "the project has errors, so the edit script can't be replayed on it".to_owned(),
        );
    }
    let mut held = Held::new(&db, program)?;
    let first = start.elapsed();
    let mut steps = Vec::new();
    for edit in edits {
        project.texts[edit.file].clone_from(&edit.text);
        let start = Clock::own();
        files[edit.file]
            .set_bytes(&mut db)
            .to(edit.text.as_bytes().to_vec());
        let errors = has_errors(&db, program);
        let front = start.elapsed();
        let update = if errors {
            None
        } else {
            Some(held.update(&db, program)?)
        };
        let time = start.elapsed();
        let split = validate(&mut db, program, &mut held, errors, front, update.as_ref());
        let differs = !errors && held.differs(&db, program);
        steps.push(HotStep {
            kind: edit.kind,
            time,
            compiled: update.as_ref().map_or(0, |u| u.compiled),
            restarts: update.as_ref().is_some_and(|u| u.restarts),
            errors,
            differs,
            split,
        });
    }
    Ok((first, steps))
}

/// The split of an update whose front end took `front`, found by timing it again, and the
/// walk that finds the changed functions, after a revision that changed nothing.
fn validate(
    db: &mut Database,
    program: Program,
    held: &mut Held,
    errors: bool,
    front: Duration,
    update: Option<&Update>,
) -> Split {
    // A revision in which nothing changed, so that what follows proves every memo it reads
    // unchanged, as after an edit, but runs none of them again.
    salsa::Database::synthetic_write(db, Durability::LOW);
    let start = Clock::own();
    has_errors(db, program);
    let mut split = Split::front_end(front, start.elapsed());
    if let (false, Some(update)) = (errors, update) {
        let start = Clock::own();
        held.counted(db, program);
        let walk = start.elapsed().min(update.codegen);
        split.validation += walk;
        split.codegen = update.codegen.saturating_sub(walk);
        split.patching = update.patching;
    }
    split
}

fn has_errors(db: &Database, program: Program) -> bool {
    stilt_types::check_in_parallel(db, program)
        .iter()
        .any(|d| d.diagnostic.is_error())
}
