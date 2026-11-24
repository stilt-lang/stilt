//! The program's engine as the language server's backend: it gives the engine each buffer the
//! editor holds, asks it what needs the program, and answers what needs only a file's text
//! itself.

use std::collections::HashMap;
use std::io;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use std::process::Command;

use stilt_lsp::{
    Backend, Completion, FileDiagnostics, Fold, Highlight, Hint, Job, Lens, Output, Place, Ran,
    Renamed, Signature, Symbol, Token, Whereabouts,
};

use stilt_ide::editor::{access, lenses, outline, syntax};

use super::At;
use crate::engine::{Answer, Query, identity, language};

/// Serves the editor on stdin and stdout until it exits.
pub(super) fn serve() -> ExitCode {
    let mut backend = Engine {
        build: identity(),
        ..Engine::default()
    };
    let input = io::BufReader::new(io::stdin());
    match stilt_lsp::serve(input, io::stdout(), &mut backend) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("stilt: {e}");
            ExitCode::from(1)
        }
    }
}

/// The program's engine, as the language server's backend.
#[derive(Debug, Default)]
struct Engine {
    /// Which build of the compiler this server is, as it started (engines.toolchains).
    build: String,
    /// The program the editor opened.
    root: Option<PathBuf>,
    /// The text of each open buffer, by its file's canonical path.
    buffers: HashMap<PathBuf, String>,
    /// The process of the engine that answered last.
    answering: Option<u32>,
}

/// The message of an engine's answer to another question than the one asked.
fn mismatched<T>() -> Result<T, String> {
    Err("the engine answered another question".to_owned())
}

impl Engine {
    /// The engine's answer to `query`, after giving the open buffers to an engine that holds
    /// none.
    fn ask(&mut self, query: &Query) -> Result<Answer, String> {
        self.stop_if_replaced();
        let root = self.root.clone().ok_or("no program is open")?;
        let unanswered = || "the program's engine doesn't answer".to_owned();
        let (engine, answer) = language(&root, query).ok_or_else(unanswered)?;
        if self.answering == Some(engine) || self.buffers.is_empty() {
            self.answering = Some(engine);
            return Ok(answer);
        }
        self.answering = Some(engine);
        for (file, text) in &self.buffers {
            let file = file.clone();
            let text = Some(text.clone());
            language(&root, &Query::Buffer { file, text }).ok_or_else(unanswered)?;
        }
        language(&root, query)
            .map(|(_, a)| a)
            .ok_or_else(unanswered)
    }

    /// Stops the server when another build replaced its executable, as an update does: it can
    /// reach no engine of its own build, and the editor starts the new build's server when this
    /// one stops (engines.toolchains).
    fn stop_if_replaced(&self) {
        if identity() != self.build {
            eprintln!(
                "stilt: another build of stilt replaced this language server's executable, so \
                 it can reach no engine of its own build; it stops, and the editor starts the new \
                 one"
            );
            std::process::exit(1);
        }
    }

    /// The engine's answer to a question about a position of a file.
    fn at(&mut self, path: &Path, offset: u32, what: At) -> Result<Answer, String> {
        let file = path.to_path_buf();
        self.ask(&Query::At { file, offset, what })
    }
}

impl Backend for Engine {
    fn open(&mut self, root: &Path) -> Result<(), String> {
        let root = root
            .canonicalize()
            .map_err(|e| format!("cannot open {}: {e}", root.display()))?;
        self.root = Some(root);
        Ok(())
    }

    fn buffer(&mut self, path: &Path, text: Option<&str>) -> Result<(), String> {
        match text {
            Some(text) => self.buffers.insert(path.to_path_buf(), text.to_owned()),
            None => self.buffers.remove(path),
        };
        let file = path.to_path_buf();
        let text = text.map(str::to_owned);
        self.ask(&Query::Buffer { file, text }).map(drop)
    }

    fn diagnostics(&mut self) -> Result<Vec<FileDiagnostics>, String> {
        match self.ask(&Query::Diagnostics)? {
            Answer::Diagnostics(files) => {
                if let Some(log) = crate::diagnostic_log::path() {
                    let seen = files.iter().flat_map(|f| {
                        f.diagnostics.iter().map(|d| crate::diagnostic_log::Seen {
                            path: &f.path,
                            code: &d.code,
                            start: d.start,
                            end: d.end,
                        })
                    });
                    crate::diagnostic_log::record(&log, "editor", seen);
                }
                Ok(files)
            }
            _ => mismatched(),
        }
    }

    fn hover(&mut self, path: &Path, offset: u32) -> Result<Option<String>, String> {
        let file = path.to_path_buf();
        match self.ask(&Query::Hover { file, offset })? {
            Answer::Hover(shown) => Ok(shown),
            _ => mismatched(),
        }
    }

    fn definition(&mut self, path: &Path, offset: u32) -> Result<Option<Place>, String> {
        let file = path.to_path_buf();
        match self.ask(&Query::Definition { file, offset })? {
            Answer::Definition(place) => Ok(place),
            _ => mismatched(),
        }
    }

    fn type_definition(&mut self, path: &Path, offset: u32) -> Result<Option<Place>, String> {
        match self.at(path, offset, At::TypeDefinition)? {
            Answer::Definition(place) => Ok(place),
            _ => mismatched(),
        }
    }

    fn completion(&mut self, path: &Path, offset: u32) -> Result<Vec<Completion>, String> {
        match self.at(path, offset, At::Completion)? {
            Answer::Completion(found) => Ok(found),
            _ => mismatched(),
        }
    }

    fn signature(&mut self, path: &Path, offset: u32) -> Result<Option<Signature>, String> {
        match self.at(path, offset, At::Signature)? {
            Answer::Signature(found) => Ok(found),
            _ => mismatched(),
        }
    }

    fn references(&mut self, path: &Path, offset: u32) -> Result<Vec<Place>, String> {
        match self.at(path, offset, At::References)? {
            Answer::References(found) => Ok(found),
            _ => mismatched(),
        }
    }

    fn highlights(&mut self, path: &Path, offset: u32) -> Result<Vec<Highlight>, String> {
        let found = self.references(path, offset)?;
        let text = match self.buffers.get(path) {
            Some(text) => text.clone(),
            None => std::fs::read_to_string(path).unwrap_or_default(),
        };
        Ok(access::highlights(
            &text,
            found.iter().filter(|p| p.path == path),
        ))
    }

    fn prepare_rename(
        &mut self,
        path: &Path,
        offset: u32,
    ) -> Result<Result<Place, String>, String> {
        match self.at(path, offset, At::PrepareRename)? {
            Answer::Renaming(found) => Ok(found),
            _ => mismatched(),
        }
    }

    fn rename(&mut self, path: &Path, offset: u32, name: &str) -> Result<Renamed, String> {
        match self.at(path, offset, At::Rename(name.to_owned()))? {
            Answer::Renamed(found) => Ok(found),
            _ => mismatched(),
        }
    }

    fn symbols(&mut self, path: &Path, text: &str) -> Vec<Symbol> {
        outline::symbols(path, text)
    }

    fn workspace_symbols(&mut self, query: &str) -> Result<Vec<Symbol>, String> {
        match self.ask(&Query::Symbols(query.to_owned()))? {
            Answer::Symbols(found) => Ok(found),
            _ => mismatched(),
        }
    }

    fn whereabouts(&mut self, path: &Path, offset: u32) -> Result<Option<Whereabouts>, String> {
        match self.at(path, offset, At::Whereabouts)? {
            Answer::Whereabouts(found) => Ok(found),
            _ => mismatched(),
        }
    }

    fn hints(&mut self, path: &Path) -> Result<Vec<Hint>, String> {
        match self.ask(&Query::Hints(path.to_path_buf()))? {
            Answer::Hints(found) => Ok(found),
            _ => mismatched(),
        }
    }

    fn tokens(&mut self, path: &Path) -> Result<Vec<Token>, String> {
        match self.ask(&Query::Tokens(path.to_path_buf()))? {
            Answer::Tokens(found) => Ok(found),
            _ => mismatched(),
        }
    }

    fn folds(&mut self, text: &str) -> Vec<Fold> {
        syntax::folds(text)
    }

    fn selections(&mut self, text: &str, offset: u32) -> Vec<(u32, u32)> {
        syntax::selections(text, offset)
    }

    fn format(&mut self, text: &str) -> Option<String> {
        syntax::format(text)
    }

    fn lenses(&mut self, path: &Path, text: &str) -> Vec<Lens> {
        self.root
            .as_deref()
            .map_or_else(Vec::new, |root| lenses::lenses(root, path, text))
    }

    fn job(&mut self, job: Job) -> Result<Command, String> {
        lenses::job(self.root.as_deref().ok_or("no program is open")?, job)
    }

    fn ran(&mut self, job: Job, output: &Output) -> Ran {
        let root = self.root.clone().unwrap_or_default();
        lenses::ran(&root, job, output)
    }
}
