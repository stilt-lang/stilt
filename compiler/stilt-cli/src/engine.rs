//! The engine: a process that holds a program's query database between commands, so that a
//! command answers from what the commands before it computed. `stilt build` right after
//! `stilt check` runs no query of the front end again (goal one-engine; Compiler
//! architecture, "The engine").
//!
//! - **Finding it.** An engine listens on a socket of its own, named after the program's
//!   canonical path and the toolchain's version, so that each version has engines of its own
//!   (engines.toolchains). A lock file beside the socket, held for the engine's life, keeps a
//!   second engine of the version from holding the same program.
//! - **Who it answers.** Only its user (engines.private): the socket lies in a directory of the
//!   user's own that no other user may open, and each end of a connection checks that the
//!   other runs as the same user ([`private`]). A command of another build of the version gets
//!   no answer, runs in its own process, and stops the engine, so that the next command starts
//!   one of its build.
//! - **Using it.** `check`, `build`, `run` and `show` on a directory program send their
//!   command to the program's engine, and print its report, which is the one they would have
//!   printed: the engine runs the same code on the same files. A command that finds none
//!   starts one and waits for it to listen. A program of one file has no engine for them, and
//!   runs in the command's own process, as does a command whose engine can't answer. `test`
//!   asks the engine of every program, a single file included, since the engine remembers the
//!   results of its tests and the files of each run whose verdict wasn't done
//!   ([`crate::test`]).
//! - **Starting.** Commands that start at once start one engine: the lock file lets one hold
//!   the program, and every other ends and leaves its command to connect to the one that
//!   holds it.
//! - **Running tests.** The engine sends `test` the diagnostics and the code of the tests to
//!   run, which `test` compiles and runs in its own process, so that a test that overflows its
//!   stack ends `test` and not the engine; `test` then sends their results back.
//! - **Sessions of the REPL.** `stilt repl`, on a directory program, keeps its
//!   front in the engine, which checks and lowers each input and sends what the session's image
//!   loads and runs (`crate::repl`). While a session is open, the engine doesn't idle.
//! - **Running programs.** A program runs in `run`'s process, but `run` asks the engine for
//!   its code, the MIR that `run` would have lowered, and compiles what it receives. It then
//!   asks at each look at the program's files, and the engine answers with what the edits
//!   since the last look change in the run: the functions whose code changed, and whether the
//!   layout of the program's values did ([`crate::run::Update`]).
//! - **Files.** Each command first takes in the edits made to the program's files since the
//!   last: a file whose time of change or size differs is read again, and a file added or
//!   removed reads the program again ([`crate::sync`]).
//! - **Clients at once.** Taking in edits writes to the database, one command at a time; every
//!   command, and every look of a run, then answers from a handle of its own, so several
//!   answer at once. A write cancels the commands answering, which then take in the edit and
//!   answer again. Each write counts as a revision, and a run's look answers with the edits of
//!   the revisions since the one it saw last, whichever command took them in.
//! - **Stopping.** An engine stops once no command has come for its idle time, two minutes
//!   unless `--idle` says otherwise, or when `stilt engine --stop` asks it to. A running
//!   program looks at its files often, so its engine never idles while it runs; once the
//!   engine is gone, the run goes on without patching its edits.
//! - **Memory.** After each command, when no other is being answered, an engine forgets the
//!   syntax trees beyond those it read last, so that its cache stays bounded (goal
//!   bounded-cache).

mod client;
mod place;
pub(crate) use place::identity;
mod private;
pub(crate) use private::{directory, without_engines};
mod server;
mod wire;

use serde::{Deserialize, Serialize};

use crate::build::Build;

pub(crate) use client::{Remote, Repl, Tests, ask, language, ran, stop};
pub(crate) use server::serve;

/// How many seconds an engine waits for a command before it stops.
pub(crate) const IDLE: u64 = 120;

/// A command that an engine answers.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum Command {
    /// `stilt check`, with `--json` or not.
    Check { json: bool },
    /// `stilt build`.
    Build(Build),
    /// `stilt show ADDRESS`, with `--json` or not, and `--expanded` or not.
    Show {
        address: String,
        json: bool,
        expanded: bool,
    },
    /// `stilt test`, with `--json` or not: what running the tests needs, then the results,
    /// which the engine remembers.
    Test { json: bool },
    /// `stilt run`: what starting the program needs, then at each look, what the edits
    /// since the last look change in the run.
    Run,
    /// `stilt repl`: the session's front, which answers each of its asks
    /// (`crate::repl`).
    Repl,
    /// The queries the engine has run since this was last asked.
    Ran,
    /// What the language server asks ([`crate::lsp`]).
    Language(Query),
    /// Stop.
    Stop,
}

/// What the language server asks the engine, each file by its canonical path and each offset a
/// byte of the file's text as the engine holds it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum Query {
    /// Hold `text` as the file's contents in place of the disk's, for every command after, or,
    /// with none, read the disk's again: an editor's buffer, open or closed.
    Buffer {
        file: std::path::PathBuf,
        text: Option<String>,
    },
    /// The diagnostics of every file that has any.
    Diagnostics,
    /// What a hover at the offset shows.
    Hover {
        file: std::path::PathBuf,
        offset: u32,
    },
    /// Where what the code names at the offset is defined.
    Definition {
        file: std::path::PathBuf,
        offset: u32,
    },
    /// A question about a position of a file ([`crate::lsp::At`]).
    At {
        file: std::path::PathBuf,
        offset: u32,
        what: crate::lsp::At,
    },
    /// The declarations of the program's files whose names match the query.
    Symbols(String),
    /// The inlay hints of a file.
    Hints(std::path::PathBuf),
    /// The semantic tokens of a file.
    Tokens(std::path::PathBuf),
}

/// The engine's answer to a [`Query`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum Answer {
    /// The buffer is held.
    Held,
    Diagnostics(Vec<stilt_lsp::FileDiagnostics>),
    Hover(Option<String>),
    Definition(Option<stilt_lsp::Place>),
    Completion(Vec<stilt_lsp::Completion>),
    Signature(Option<stilt_lsp::Signature>),
    References(Vec<stilt_lsp::Place>),
    /// The name a rename would change, or why it can't.
    Renaming(Result<stilt_lsp::Place, String>),
    Renamed(stilt_lsp::Renamed),
    Whereabouts(Option<stilt_lsp::Whereabouts>),
    Symbols(Vec<stilt_lsp::Symbol>),
    Hints(Vec<stilt_lsp::Hint>),
    Tokens(Vec<stilt_lsp::Token>),
}
