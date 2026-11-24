//! The language server (goal one-engine; Compiler architecture, "The engine"). It speaks the
//! Language Server Protocol to an editor over stdin and stdout, and answers from a
//! [`Backend`]: `stilt lsp` gives it the program's engine, which the command line, agents and
//! running programs share, so the editor sees what they see.
//!
//! - **Diagnostics as the user types.** The text of each buffer the editor opens or changes
//!   replaces its file's in the engine until the editor closes it, and each change publishes
//!   the diagnostics of every file of the program. Changes that arrive together publish once.
//!   A diagnostic's notes are its related information, its code links to its page of the error
//!   index, and a warning about code that does nothing is marked unnecessary.
//! - **Hover.** A function's signature with its inferred facts and its doc, a variable's
//!   inferred type, a type's definition with its doc, and a macro use's expansion.
//! - **Navigation.** The definition of a name, which is its declaration, its type's
//!   definition, its references and their highlights in the file, those that bind or assign it
//!   apart, and the declarations of a file, or of the program, as symbols.
//! - **Writing.** Completion of the names in scope, of members after a `.`, of modules after
//!   `use` and of keywords, a call written with a placeholder for each parameter and a keyword
//!   with its construct, where the editor expands snippets; the signature of the function a
//!   call calls; renaming across the program's files; and formatting, as `stilt fmt` formats.
//! - **Reading.** Inlay hints of inferred types and facts, semantic tokens, folding ranges and
//!   selection ranges.
//! - **Code actions.** The fixes of the diagnostics at a range (goal one-diagnostic-shape), each an
//!   edit of the file, a diagnostic's only fix its preferred one, and every fix of a file at
//!   once, `source.fixAll.stilt`, which an editor may run on save.
//! - **Code lenses.** Above each test, doc example and property, a lens that runs the program's
//!   tests, and above the `main` of its `main.lt` one that runs it, each a process of
//!   `stilt test` or `stilt run` that the editor's lens stops; each case's result, and the
//!   program's exit status with its last line of output, show inline until a file changes. Visual
//!   Studio Code's extension has its own, in its test explorer, so it is offered none.
//! - **Files on disk.** A change the editor reports to a file it watches publishes the
//!   diagnostics again, since the engine reads the disk as it answers.
//!
//! The backend works in bytes of a file's text; this crate turns them into the protocol's
//! positions, counted in UTF-16, and back.
//!
//! Its place among the crates (`compiler/README.md`): it depends on no crate of the compiler;
//! `stilt-cli` gives it a [`Backend`] that answers from the program's engine.
#![warn(missing_docs)]

#[rustfmt::skip]
mod codes;
mod convert;
mod jobs;
mod model;
mod requests;
mod server;
mod text;
mod tokens;
mod transport;

use std::path::Path;
use std::process::Command;

pub use model::*;
pub use server::serve;
pub use text::uri;

/// What the server asks of the program, each path a file's canonical path and each offset a
/// byte of its text as the backend holds it. An error is a message for the editor's log.
///
/// # Errors
///
/// Each method that returns a `Result` fails when the program can't answer.
#[allow(
    clippy::missing_errors_doc,
    reason = "every method fails in the one way the trait's doc gives"
)]
pub trait Backend {
    /// Opens the program at `root`, the folder the editor opened.
    fn open(&mut self, root: &Path) -> Result<(), String>;

    /// Holds `text` as the contents of the file at `path`, in place of what the disk holds,
    /// or, with `None`, goes back to the disk.
    fn buffer(&mut self, path: &Path, text: Option<&str>) -> Result<(), String>;

    /// The diagnostics of every file of the program that has any.
    fn diagnostics(&mut self) -> Result<Vec<FileDiagnostics>, String>;

    /// What a hover at `offset` of the file at `path` shows, in Markdown, if anything.
    fn hover(&mut self, path: &Path, offset: u32) -> Result<Option<String>, String>;

    /// Where what the code names at `offset` of the file at `path` is defined, if anywhere.
    fn definition(&mut self, path: &Path, offset: u32) -> Result<Option<Place>, String>;

    /// Where the type of what the code names at `offset` is defined, if anywhere.
    fn type_definition(&mut self, path: &Path, offset: u32) -> Result<Option<Place>, String>;

    /// The names that may be written at `offset`, which may be in broken code.
    fn completion(&mut self, path: &Path, offset: u32) -> Result<Vec<Completion>, String>;

    /// The signature of the function that the call around `offset` calls.
    fn signature(&mut self, path: &Path, offset: u32) -> Result<Option<Signature>, String>;

    /// Every place, in every file of the program, that names what the code names at `offset`,
    /// its declaration included.
    fn references(&mut self, path: &Path, offset: u32) -> Result<Vec<Place>, String>;

    /// Every place of the file at `path` that names what the code names at `offset`, each
    /// marked where code writes it.
    fn highlights(&mut self, path: &Path, offset: u32) -> Result<Vec<Highlight>, String>;

    /// The name at `offset` that a rename would change, or why it can't be renamed.
    fn prepare_rename(&mut self, path: &Path, offset: u32)
    -> Result<Result<Place, String>, String>;

    /// The edits that rename what the code names at `offset` to `name`.
    fn rename(&mut self, path: &Path, offset: u32, name: &str) -> Result<Renamed, String>;

    /// The declarations of the file at `path`, whose text is `text`.
    fn symbols(&mut self, path: &Path, text: &str) -> Vec<Symbol>;

    /// The declarations of every file of the program whose names match `query`.
    fn workspace_symbols(&mut self, query: &str) -> Result<Vec<Symbol>, String>;

    /// The module of the file at `path`, and the function around `offset`.
    fn whereabouts(&mut self, path: &Path, offset: u32) -> Result<Option<Whereabouts>, String>;

    /// The inlay hints of the file at `path`.
    fn hints(&mut self, path: &Path) -> Result<Vec<Hint>, String>;

    /// The semantic tokens of the file at `path`, in order.
    fn tokens(&mut self, path: &Path) -> Result<Vec<Token>, String>;

    /// The spans of `text` that may be folded.
    fn folds(&mut self, text: &str) -> Vec<Fold>;

    /// The spans of `text` around `offset`, from the smallest out.
    fn selections(&mut self, text: &str, offset: u32) -> Vec<(u32, u32)>;

    /// `text` as `stilt fmt` formats it, or `None` when it has a syntax error.
    fn format(&mut self, text: &str) -> Option<String>;

    /// The code lenses of the file at `path`, whose text is `text`.
    fn lenses(&mut self, path: &Path, text: &str) -> Vec<Lens>;

    /// The process that runs `job`, which the server gives an empty standard input.
    fn job(&mut self, job: Job) -> Result<Command, String>;

    /// What the process of `job` found, from its output.
    fn ran(&mut self, job: Job, output: &Output) -> Ran;
}
