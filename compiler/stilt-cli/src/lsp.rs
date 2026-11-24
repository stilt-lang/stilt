//! `stilt lsp`: the language server (goal one-engine; Compiler architecture, "The
//! engine"). It speaks the protocol to the editor on stdin and stdout ([`stilt_lsp`]) and asks
//! the engine of the program the editor opened, starting one when none runs, so the editor,
//! the command line, agents and running programs share one database: a fix that works in the
//! editor works in CI, and a running program receives each edit as the editor does. The text
//! of the editor's open buffers replaces their files' in the engine until the editor closes
//! them, so every client reads them. The answers come from [`stilt_ide::editor`].
//!
//! An engine stops once idle, and the one started next holds none of the buffers: each answer
//! names its engine's process, and a new one is given every open buffer before it answers.
//!
//! The engine answers what needs the program; what needs only a file's text, its folding and
//! selection ranges, its outline and its formatting, is answered here.

mod backend;

use std::process::ExitCode;

use serde::{Deserialize, Serialize};
use stilt_db::{Database, Program, SourceFile};
use stilt_ide::editor::{
    Completed, Paths, completion, references, signature, type_definition, whereabouts,
};

use crate::engine::Answer;

/// Serves the editor on stdin and stdout until it exits.
pub(crate) fn command() -> ExitCode {
    backend::serve()
}

/// What the language server asks about a position of a file.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum At {
    TypeDefinition,
    Completion,
    Signature,
    References,
    /// The name a rename would change.
    PrepareRename,
    /// The edits that rename the name to this one.
    Rename(String),
    Whereabouts,
}

/// The answer to a question about the position `offset` of `file`. Completion here answers
/// from the file as it is; the engine checks it again without a `.` that ends a line first
/// ([`Completed::Patch`]).
pub(crate) fn answer(
    db: &Database,
    program: Program,
    paths: &Paths,
    (file, offset): (SourceFile, u32),
    what: &At,
) -> Answer {
    match what {
        At::TypeDefinition => Answer::Definition(type_definition(db, program, paths, file, offset)),
        At::Completion => match completion(db, program, file, offset) {
            Completed::Done(found) => Answer::Completion(found),
            Completed::Patch { .. } => Answer::Completion(Vec::new()),
        },
        At::Signature => Answer::Signature(signature::signature(db, program, file, offset)),
        At::References => {
            Answer::References(references::references(db, program, paths, file, offset))
        }
        At::PrepareRename => {
            Answer::Renaming(references::prepare(db, program, paths, file, offset))
        }
        At::Rename(name) => {
            Answer::Renamed(references::rename(db, program, paths, (file, offset), name))
        }
        At::Whereabouts => Answer::Whereabouts(Some(whereabouts(db, program, file, offset))),
    }
}
