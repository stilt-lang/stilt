//! The image's side of a REPL session (repl.answers, repl.running-inputs, repl.program-edits and
//! repl.bindings-across-edits): the image that holds the code of the inputs and of what they reach
//! of the program, patched as the program changes, and the values of the session's bindings. Each
//! answer of the session's front is taken in here: its reports written, the bindings it drops
//! dropped, its functions loaded, and its input run on a thread of its own, then answered.

use std::io::Write as _;
use std::path::PathBuf;

use stilt_codegen_clif::Image;
use stilt_runtime::{Evaluated, Value};

use super::front::{Answer, Run};

/// A binding's value, as the session holds it.
struct Held {
    id: u32,
    name: String,
    value: Value,
}

/// The image's side of a session.
pub(super) struct Session {
    image: Image,
    values: Vec<Held>,
}

impl Session {
    /// A session whose program's files have the paths `files`, by the indexes its locations
    /// use, and are at `paths` for debuggers.
    pub(super) fn new(files: Vec<String>, paths: Vec<PathBuf>) -> Result<Self, String> {
        stilt_runtime::prepare_session(files);
        let mut image = Image::new()?;
        image.set_files(paths);
        Ok(Self {
            image,
            values: Vec::new(),
        })
    }

    /// The ids of the bindings it holds, in the order they were bound.
    pub(super) fn live(&self) -> Vec<u32> {
        self.values.iter().map(|h| h.id).collect()
    }

    /// Takes in an answer of the front, and gives the status the session ends with, if an input
    /// ended it.
    pub(super) fn take(&mut self, answer: Answer) -> Option<i32> {
        eprint!("{}", answer.report);
        self.values.retain(|h| !answer.dropped.contains(&h.id));
        if let Some(files) = answer.files {
            stilt_runtime::prepare_session(files);
        }
        if let Err(message) = self.image.load(&answer.functions) {
            eprintln!("stilt: {}", crate::bug::internal(message));
            return None;
        }
        let ended = answer.run.and_then(|run| self.run(run));
        let _ = std::io::stdout().flush();
        ended
    }

    /// Runs an input, and answers it.
    fn run(&mut self, run: Run) -> Option<i32> {
        let entry = match self.image.entry_of(&run.entry) {
            Ok(entry) => entry,
            Err(message) => {
                eprintln!("stilt: {}", crate::bug::internal(message));
                return None;
            }
        };
        let values: Option<Vec<&Value>> = (run.params.iter())
            .map(|id| self.values.iter().find(|h| h.id == *id).map(|h| &h.value))
            .collect();
        let Some(values) = values else {
            eprintln!("stilt: internal error: the input takes a binding the session doesn't hold");
            return None;
        };
        let heaps: Vec<Vec<bool>> = run.binds.iter().map(|b| b.heap.clone()).collect();
        let (evaluated, made) = stilt_runtime::evaluate(entry, &values, &heaps);
        match evaluated {
            Evaluated::Value(shown) => {
                let mut out = std::io::stdout().lock();
                if let Some(ty) = &run.ty {
                    // A value whose type has no `Show` answers with its type alone.
                    let _ = if shown.is_empty() {
                        writeln!(out, "{ty}")
                    } else {
                        writeln!(out, "{shown}: {ty}")
                    };
                }
                for (bind, value) in run.binds.into_iter().zip(made) {
                    let _ = writeln!(out, "{}: {}", bind.name, bind.ty);
                    self.values.retain(|h| h.name != bind.name);
                    self.values.push(Held {
                        id: bind.id,
                        name: bind.name,
                        value,
                    });
                }
                None
            }
            Evaluated::Raised(shown) => {
                eprintln!("error: {shown}");
                None
            }
            Evaluated::Panicked => None,
            Evaluated::Ended(status) => Some(status),
        }
    }
}
