//! The engine's answers to the language server ([`crate::lsp`]): it holds the text of the
//! editor's buffers in place of their files', so that every command after reads them, and
//! answers each question from a handle of its own, as it answers a command.

use std::panic::AssertUnwindSafe;
use std::path::{Path, PathBuf};

use stilt_db::{Database, Program, SourceFile};

use super::{Engine, Unanswered};
use crate::engine::wire::Reply;
use crate::engine::{Answer, Query};
use crate::lsp::At;
use stilt_ide::editor::Completed;

/// Each file of the program with its canonical path.
type Paths = [(SourceFile, PathBuf)];

impl Engine {
    pub(super) fn language(&self, query: Query) -> Reply {
        let answer = match query {
            Query::Buffer { file, text } => {
                self.held().synced.buffer(&file, text);
                Ok(Answer::Held)
            }
            Query::Diagnostics => self.with_paths(|db, program, paths| {
                Answer::Diagnostics(stilt_ide::editor::diagnostics(db, program, paths))
            }),
            Query::Hover { file, offset } => self.with_paths(|db, program, paths| {
                let source = source(paths, &file);
                Answer::Hover(source.and_then(|s| crate::show::hover(db, program, s, offset)))
            }),
            Query::Definition { file, offset } => self.with_paths(|db, program, paths| {
                let found = source(paths, &file)
                    .and_then(|s| crate::show::definition(db, program, s, offset));
                Answer::Definition(found.and_then(|(f, range)| place(paths, f, range)))
            }),
            Query::At {
                file,
                offset,
                what: At::Completion,
            } => self.complete(&file, offset),
            Query::At { file, offset, what } => {
                self.with_paths(|db, program, paths| match source(paths, &file) {
                    Some(s) => crate::lsp::answer(db, program, paths, (s, offset), &what),
                    None => nothing(&what),
                })
            }
            Query::Symbols(query) => self.with_paths(|db, program, paths| {
                Answer::Symbols(stilt_ide::editor::program_symbols(
                    db, program, paths, &query,
                ))
            }),
            Query::Hints(file) => self.with_paths(|db, program, paths| {
                let found = source(paths, &file).map(|s| stilt_ide::editor::hints(db, program, s));
                Answer::Hints(found.unwrap_or_default())
            }),
            Query::Tokens(file) => self.with_paths(|db, program, paths| {
                let found = source(paths, &file).map(|s| stilt_ide::editor::tokens(db, program, s));
                Answer::Tokens(found.unwrap_or_default())
            }),
        };
        match answer {
            Ok(answer) => Reply::Language {
                engine: std::process::id(),
                answer,
            },
            Err(why) => Reply::Elsewhere(why.message()),
        }
    }

    /// What may be written at `offset` of `file`. After a `.` whose receiver has no type, as
    /// when the `.` leaves its function with a syntax error, the file is checked once more with
    /// the `.` and the word after it taken out, and its buffer then put back.
    fn complete(&self, file: &Path, offset: u32) -> Result<Answer, Unanswered> {
        let first = self.with_paths(|db, program, paths| {
            source(paths, file).map(|s| stilt_ide::editor::completion(db, program, s, offset))
        })?;
        let (text, receiver) = match first {
            Some(Completed::Patch { text, receiver }) => (text, receiver),
            Some(Completed::Done(found)) => return Ok(Answer::Completion(found)),
            None => return Ok(Answer::Completion(Vec::new())),
        };
        let found = self.with_patched(file, text, |db, program, paths| {
            source(paths, file)
                .map(|s| stilt_ide::editor::members(db, program, s, receiver))
                .unwrap_or_default()
        })?;
        Ok(Answer::Completion(found))
    }

    /// `f` on the program with `text` held as the contents of `file`, then the file's buffer, or
    /// its disk's contents, put back. The program is held throughout, so no other command reads
    /// the text.
    fn with_patched<T>(
        &self,
        file: &Path,
        text: String,
        f: impl FnOnce(&Database, Program, &Paths) -> T,
    ) -> Result<T, Unanswered> {
        let mut held = self.held();
        let before = held.synced.buffered(file);
        held.synced.buffer(file, Some(text));
        let synced = held.sync().map_err(Unanswered::Unreadable);
        let answer = synced.and_then(|_| {
            let (db, program, paths) = (held.db.clone(), held.synced.program, held.synced.paths());
            let answer = salsa::Cancelled::catch(AssertUnwindSafe(|| f(&db, program, &paths)));
            answer.map_err(|_| Unanswered::Panicked)
        });
        held.synced.buffer(file, before);
        answer
    }

    /// `f` on the program as its files and buffers are now, with each file's path. A question
    /// that an edit cancels takes the edit in and is answered again.
    fn with_paths<T>(
        &self,
        mut f: impl FnMut(&Database, Program, &Paths) -> T,
    ) -> Result<T, Unanswered> {
        loop {
            let (db, program, paths) = {
                let mut held = self.held();
                held.sync().map_err(Unanswered::Unreadable)?;
                (held.db.clone(), held.synced.program, held.synced.paths())
            };
            match salsa::Cancelled::catch(AssertUnwindSafe(|| f(&db, program, &paths))) {
                Ok(value) => return Ok(value),
                Err(salsa::Cancelled::PropagatedPanic) => return Err(Unanswered::Panicked),
                Err(_) => {}
            }
        }
    }
}

/// The answer to a question about a file that isn't the program's.
fn nothing(what: &At) -> Answer {
    match what {
        At::TypeDefinition => Answer::Definition(None),
        At::Completion => Answer::Completion(Vec::new()),
        At::Signature => Answer::Signature(None),
        At::References => Answer::References(Vec::new()),
        At::PrepareRename => Answer::Renaming(Err("the file isn't the program's".to_owned())),
        At::Rename(_) => Answer::Renamed(Err("the file isn't the program's".to_owned())),
        At::Whereabouts => Answer::Whereabouts(None),
    }
}

/// The program's file at `path`.
fn source(paths: &Paths, path: &Path) -> Option<SourceFile> {
    paths.iter().find(|(_, p)| p == path).map(|(f, _)| *f)
}

/// A span of one of the program's files, by the file's path; none in the standard library,
/// which has no file an editor could open.
fn place(
    paths: &Paths,
    file: SourceFile,
    range: stilt_syntax::TextRange,
) -> Option<stilt_lsp::Place> {
    let (_, path) = paths.iter().find(|(f, _)| *f == file)?;
    Some(stilt_lsp::Place {
        path: path.clone(),
        start: range.start().into(),
        end: range.end().into(),
    })
}
