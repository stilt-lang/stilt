//! The fake backend's answer to each of the server's questions.

use std::path::Path;
use std::process::Command;

use super::{Fake, PATHS, TOKENS};
use stilt_lsp::{
    Backend, Completion, FileDiagnostics, Fold, FoldSort, Highlight, Hint, Job, Lens, Output,
    Place, Ran, Renamed, Signature, Symbol, Token, Whereabouts,
};

impl Backend for Fake<'_> {
    fn open(&mut self, _root: &Path) -> Result<(), String> {
        self.answer(|_| ())
    }

    fn buffer(&mut self, path: &Path, text: Option<&str>) -> Result<(), String> {
        match text {
            Some(text) => self.buffers.insert(path.to_path_buf(), text.to_owned()),
            None => self.buffers.remove(path),
        };
        self.answer(|_| ())
    }

    fn diagnostics(&mut self) -> Result<Vec<FileDiagnostics>, String> {
        self.answer(|s| {
            s.list(false, |s| {
                let path = s.path();
                let text = s.text_of(&path);
                let diagnostics = s.list(true, |s| s.diagnostic(&text));
                FileDiagnostics { path, diagnostics }
            })
        })
    }

    fn hover(&mut self, _path: &Path, _offset: u32) -> Result<Option<String>, String> {
        self.answer(Fake::maybe)
    }

    fn definition(&mut self, _path: &Path, _offset: u32) -> Result<Option<Place>, String> {
        self.answer(|s| s.bytes.flag().then(|| s.place()))
    }

    fn type_definition(&mut self, path: &Path, offset: u32) -> Result<Option<Place>, String> {
        self.definition(path, offset)
    }

    fn completion(&mut self, _path: &Path, _offset: u32) -> Result<Vec<Completion>, String> {
        self.answer(|s| s.list(true, Fake::completion))
    }

    fn signature(&mut self, _path: &Path, _offset: u32) -> Result<Option<Signature>, String> {
        self.answer(|s| {
            let label = s.bytes.words();
            let params = s.list(true, |s| s.span(&label));
            let docs = s.maybe();
            let active = s.bytes.u32();
            s.bytes.flag().then_some(Signature {
                label,
                params,
                active,
                docs,
            })
        })
    }

    fn references(&mut self, _path: &Path, _offset: u32) -> Result<Vec<Place>, String> {
        self.answer(|s| s.list(true, Fake::place))
    }

    fn highlights(&mut self, path: &Path, _offset: u32) -> Result<Vec<Highlight>, String> {
        let text = self.text_of(path);
        self.answer(|s| {
            s.list(true, |s| {
                let (start, end) = s.span(&text);
                let write = s.bytes.flag();
                Highlight { start, end, write }
            })
        })
    }

    fn prepare_rename(
        &mut self,
        _path: &Path,
        _offset: u32,
    ) -> Result<Result<Place, String>, String> {
        self.answer(|s| {
            if s.bytes.flag() {
                Ok(s.place())
            } else {
                Err(s.bytes.words())
            }
        })
    }

    fn rename(&mut self, _path: &Path, _offset: u32, _name: &str) -> Result<Renamed, String> {
        self.answer(|s| match s.bytes.below(4) {
            0 => Err(s.bytes.words()),
            _ => Ok(s.list(false, |s| {
                let path = s.path();
                let text = s.text_of(&path);
                (path, s.list(true, |s| s.edit(&text)))
            })),
        })
    }

    fn symbols(&mut self, path: &Path, _text: &str) -> Vec<Symbol> {
        self.symbols_of(path, 0)
    }

    fn workspace_symbols(&mut self, _query: &str) -> Result<Vec<Symbol>, String> {
        self.answer(|s| {
            let mut found = Vec::new();
            for path in PATHS {
                found.extend(s.symbols_of(Path::new(path), 0));
            }
            found
        })
    }

    fn whereabouts(&mut self, _path: &Path, _offset: u32) -> Result<Option<Whereabouts>, String> {
        self.answer(|s| {
            s.bytes.flag().then(|| Whereabouts {
                module: s.bytes.words(),
                tier: s.bytes.words(),
                function: s.maybe(),
            })
        })
    }

    fn hints(&mut self, path: &Path) -> Result<Vec<Hint>, String> {
        let text = self.text_of(path);
        self.answer(|s| s.list(true, |s| s.hint(&text)))
    }

    fn tokens(&mut self, path: &Path) -> Result<Vec<Token>, String> {
        let text = self.text_of(path);
        self.answer(|s| {
            let mut tokens = s.list(true, |s| {
                let (start, end) = s.span(&text);
                let sort = s.bytes.pick(&TOKENS);
                let modifiers = s.bytes.u32();
                Token {
                    start,
                    end,
                    sort,
                    modifiers,
                }
            });
            // In order, as the trait has them, or as they came.
            if s.bytes.flag() {
                tokens.sort_by_key(|t| t.start);
            }
            tokens
        })
    }

    fn folds(&mut self, text: &str) -> Vec<Fold> {
        self.list(true, |s| {
            let (start, end) = s.span(text);
            let sort = s
                .bytes
                .pick(&[FoldSort::Code, FoldSort::Comment, FoldSort::Imports]);
            Fold { start, end, sort }
        })
    }

    fn selections(&mut self, text: &str, _offset: u32) -> Vec<(u32, u32)> {
        self.list(true, |s| s.span(text))
    }

    fn format(&mut self, text: &str) -> Option<String> {
        match self.bytes.below(4) {
            0 => None,
            1 => Some(text.to_owned()),
            2 => Some(self.bytes.words()),
            _ => Some(format!("{text}{}", self.bytes.words())),
        }
    }

    fn lenses(&mut self, _path: &Path, text: &str) -> Vec<Lens> {
        self.list(true, |s| Lens {
            at: s.offset(text),
            job: s.bytes.pick(&[Job::Tests, Job::Main]),
        })
    }

    /// No job runs: a fuzz input starts no process.
    fn job(&mut self, _job: Job) -> Result<Command, String> {
        Err("the fuzz backend runs no job".to_owned())
    }

    fn ran(&mut self, _job: Job, _output: &Output) -> Ran {
        Ran::default()
    }
}
