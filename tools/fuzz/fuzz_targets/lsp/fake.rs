//! A backend that answers from the fuzz input rather than from a program's engine. Its answers
//! hold what an engine shouldn't give but a server must survive: offsets past the end of the
//! text or inside a character, spans that end before they start, lists empty or long, lines
//! past the last, and text of characters of every width.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use stilt_lsp::{
    Completion, Diagnostic, Edit, Fix, Hint, HintPart, HintSort, Note, Place, Sort, Symbol,
    TokenSort,
};

use crate::bytes::Bytes;

/// The paths the backend names, those of the URIs the editor sends: none is on disk, so the
/// server reads each as empty unless the editor has it open. The last is the path of a
/// request whose URI isn't a file's.
pub const PATHS: [&str; 4] = [
    "/stilt-fuzz/main.lt",
    "/stilt-fuzz/\u{e9}t\u{e9} \u{1F600}.lt",
    "/stilt-fuzz/lib/other.lt",
    "",
];

const SORTS: [Sort; 15] = [
    Sort::Local,
    Sort::Parameter,
    Sort::Function,
    Sort::Method,
    Sort::Field,
    Sort::Variant,
    Sort::Type,
    Sort::Trait,
    Sort::Constant,
    Sort::Test,
    Sort::Macro,
    Sort::Effect,
    Sort::Module,
    Sort::Keyword,
    Sort::Impl,
];

const TOKENS: [TokenSort; 24] = [
    TokenSort::Keyword,
    TokenSort::Boolean,
    TokenSort::SelfKeyword,
    TokenSort::Effect,
    TokenSort::Type,
    TokenSort::Trait,
    TokenSort::TypeParameter,
    TokenSort::RowVariable,
    TokenSort::Function,
    TokenSort::Method,
    TokenSort::Parameter,
    TokenSort::Variable,
    TokenSort::Field,
    TokenSort::Variant,
    TokenSort::Module,
    TokenSort::Macro,
    TokenSort::Fragment,
    TokenSort::Comment,
    TokenSort::String,
    TokenSort::EscapeSequence,
    TokenSort::Interpolation,
    TokenSort::FormatSpecifier,
    TokenSort::Number,
    TokenSort::Operator,
];

/// The codes of diagnostics: ones the server marks, one the error index has no page for, and
/// none.
const CODES: [&str; 8] = [
    "E0001", "W0001", "W0002", "W0300", "W0301", "W0500", "W9999", "",
];

pub struct Fake<'a> {
    bytes: Bytes<'a>,
    /// The text the editor holds of each file, as the server gives it.
    buffers: HashMap<PathBuf, String>,
}

impl<'a> Fake<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Fake {
            bytes: Bytes::cycling(data),
            buffers: HashMap::new(),
        }
    }

    fn text_of(&self, path: &Path) -> String {
        self.buffers.get(path).cloned().unwrap_or_default()
    }

    /// `Err` one time in eight, as an engine that can't answer.
    fn answer<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> Result<T, String> {
        if self.bytes.below(8) == 0 {
            Err(self.bytes.words())
        } else {
            Ok(f(self))
        }
    }

    /// A byte of `text`, or not one: the start, the end, past it, inside a character, after a
    /// line's end, anywhere.
    fn offset(&mut self, text: &str) -> u32 {
        let len = text.len();
        let anywhere = usize::from(self.bytes.byte()) * len / 255;
        let n = match self.bytes.below(10) {
            0 => 0,
            1 => len,
            2 => len + 1,
            3 => return u32::MAX,
            4 => usize::from(self.bytes.u16()),
            5 => {
                let inside: Vec<usize> = (text.char_indices())
                    .filter(|(_, c)| c.len_utf8() > 1)
                    .map(|(i, _)| i + 1)
                    .collect();
                if inside.is_empty() {
                    anywhere
                } else {
                    inside[self.bytes.below(inside.len())]
                }
            }
            6 => anywhere,
            7 => text.find('\n').map_or(0, |n| n + 1),
            8 => len.saturating_sub(1),
            _ => (0..=anywhere)
                .rev()
                .find(|&i| text.is_char_boundary(i))
                .unwrap_or(0),
        };
        u32::try_from(n).unwrap_or(u32::MAX)
    }

    /// Two offsets, in either order.
    fn span(&mut self, text: &str) -> (u32, u32) {
        (self.offset(text), self.offset(text))
    }

    /// The length of a list: none, a few or many when `long`, and otherwise at most three.
    fn list<T>(&mut self, long: bool, mut f: impl FnMut(&mut Self) -> T) -> Vec<T> {
        let n = match self.bytes.below(if long { 8 } else { 4 }) {
            5 => 32,
            6 => 128,
            7 => 256,
            n => n,
        };
        (0..n).map(|_| f(self)).collect()
    }

    /// A line, counted from 1: none, the first, any, or the last there can be.
    fn line(&mut self) -> u32 {
        match self.bytes.below(4) {
            0 => 0,
            1 => 1,
            2 => u32::from(self.bytes.byte()),
            _ => u32::MAX,
        }
    }

    fn maybe(&mut self) -> Option<String> {
        self.bytes.flag().then(|| self.bytes.words())
    }

    fn path(&mut self) -> PathBuf {
        PathBuf::from(self.bytes.pick(&PATHS))
    }

    fn place(&mut self) -> Place {
        let path = self.path();
        let (start, end) = self.span(&self.text_of(&path));
        Place { path, start, end }
    }

    fn edit(&mut self, text: &str) -> Edit {
        let (start, end) = self.span(text);
        let text = self.bytes.words();
        Edit { start, end, text }
    }

    fn diagnostic(&mut self, text: &str) -> Diagnostic {
        let (start, end) = self.span(text);
        let fixes = self.list(false, |s| Fix {
            title: s.bytes.words(),
            edits: s.list(false, |s| s.edit(text)),
        });
        let notes = self.list(false, |s| {
            let (start, end) = s.span(text);
            let text = s.bytes.words();
            Note { start, end, text }
        });
        Diagnostic {
            start,
            end,
            error: self.bytes.flag(),
            code: self.bytes.pick(&CODES).to_owned(),
            message: self.bytes.words(),
            fixes,
            notes,
        }
    }

    fn completion(&mut self) -> Completion {
        let label = self.bytes.words();
        let detail = match self.bytes.below(5) {
            0 => None,
            1 => Some(format!("{label}(x: Int) -> Int")),
            2 => Some(label.clone()),
            3 => Some("x: Int".to_owned()),
            _ => Some(self.bytes.words()),
        };
        let insert = match self.bytes.below(4) {
            0 => None,
            1 => Some(format!("{label}(${{1:x}})$0")),
            2 => Some(format!("{label}()$0")),
            _ => Some(self.bytes.words()),
        };
        Completion {
            label,
            sort: self.bytes.pick(&SORTS),
            detail,
            docs: self.maybe(),
            insert,
        }
    }

    /// The symbols of the file at `path`, nested at most three deep.
    fn symbols_of(&mut self, path: &Path, depth: usize) -> Vec<Symbol> {
        let text = self.text_of(path);
        if depth > 2 {
            return Vec::new();
        }
        self.list(depth == 0, |s| {
            let (start, end) = s.span(&text);
            let (name_start, name_end) = s.span(&text);
            Symbol {
                name: s.bytes.words(),
                sort: s.bytes.pick(&SORTS),
                detail: s.maybe(),
                path: path.to_path_buf(),
                start,
                end,
                name_start,
                name_end,
                children: s.symbols_of(path, depth + 1),
            }
        })
    }

    fn hint(&mut self, text: &str) -> Hint {
        let sort = self
            .bytes
            .pick(&[HintSort::Type, HintSort::Facts, HintSort::Causes]);
        let parts = self.list(false, |s| HintPart {
            text: s.bytes.words(),
            meaning: s.maybe(),
            causes: s.list(false, |s| (s.line(), s.bytes.words())),
        });
        Hint {
            at: self.offset(text),
            label: self.bytes.words(),
            sort,
            parts,
        }
    }
}

#[path = "answers.rs"]
mod answers;
