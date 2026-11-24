//! What a program shows of itself, to people and to editors (goal one-engine): the views of
//! `stilt show` ([`show`]), code with its inferred facts written in, and the answers of the
//! language server ([`editor`]): hover, completion, references and the rest. Each reads a
//! program from its database and returns plain values, so `stilt`, its engine and the
//! playground print the same.
//!
//! [`at`] gives a diagnostic its place in the program and its fixes as edits of parts, as
//! `check --json` reports them.

#![warn(missing_docs)]

pub mod at;
pub mod editor;
pub mod show;

use stilt_db::{Database, SourceFile};

/// The text of `file`, with any bytes that aren't UTF-8 replaced.
#[must_use]
pub fn text(db: &Database, file: SourceFile) -> String {
    String::from_utf8_lossy(file.bytes(db)).into_owned()
}
