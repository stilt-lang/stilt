//! Where a REPL session's front is held (repl.sessions): in the program's engine, which a
//! directory program or a package has, or in a database of the REPL's own, that of a program
//! whose engine can't answer, or of no program at all, whose one module `main` is empty, so that
//! inputs see the prelude alone.

use std::path::Path;

use serde::{Deserialize, Serialize};
use stilt_db::{Database, Program};
use stilt_rc::Counted;

use super::front::{Answer, Ask, Front};
use crate::engine::Repl;
use crate::sync::Synced;

/// What a session reports first, the program's diagnostics if it has errors, and the paths of
/// the program's files, by the indexes its locations use.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct Opened {
    pub(crate) report: String,
    pub(crate) files: Vec<String>,
}

/// A session's front, held in a database of the REPL's own.
pub(super) struct Here {
    db: Database,
    /// The program's files, watched, unless there is no program.
    synced: Option<Synced>,
    program: Program,
    counted: Counted,
    front: Front,
}

/// Where a session's front is held.
pub(super) enum Held {
    Here(Box<Here>),
    Engine(Repl),
}

impl Held {
    /// The front of the program at `path`, if it holds one, and otherwise of no program.
    pub(super) fn open(path: &Path) -> Result<(Self, Opened), String> {
        let program = path.join("main.lt").is_file() || path.join("stilt.toml").is_file();
        if program && let Some((repl, opened)) = Repl::open(path) {
            return Ok((Held::Engine(repl), opened));
        }
        let db = Database::default();
        let (synced, program) = if program {
            let synced = Synced::load(&db, path)?;
            let program = synced.program;
            (Some(synced), program)
        } else {
            let main =
                stilt_db::source_file(&db, "main.lt".into(), vec!["main".into()], Vec::new());
            (None, stilt_db::program(&db, vec![main]))
        };
        let (front, report, files) = Front::open(&db, program);
        let here = Here {
            db,
            synced,
            program,
            counted: Counted::default(),
            front,
        };
        Ok((Held::Here(Box::new(here)), Opened { report, files }))
    }

    /// The front's answer to `ask`, once the edits of the program's files since the last are
    /// taken in, or why there is none.
    pub(super) fn ask(&mut self, ask: &Ask) -> Result<Answer, String> {
        match self {
            Held::Here(here) => {
                let Here {
                    db,
                    synced,
                    program,
                    counted,
                    front,
                } = &mut **here;
                let mut unreadable = String::new();
                if let Some(synced) = synced {
                    if let Err(message) = synced.sync(db) {
                        unreadable = format!("stilt: {message}\n");
                    }
                    *program = synced.program;
                }
                let mut answer = front.ask(db, *program, counted, ask);
                answer.report.insert_str(0, &unreadable);
                Ok(answer)
            }
            Held::Engine(repl) => repl.ask(ask).map_err(|_| {
                "the program's engine stopped answering, so the session ends".to_owned()
            }),
        }
    }

    /// Ends the session's use of its database, as a command's ends.
    pub(super) fn close(self) {
        if let Held::Here(here) = self {
            let Here { db, .. } = *here;
            crate::end(db);
        }
    }
}
