//! The parts that `show` shows (edits.parts and edits.showing-parts): any declaration of a module
//! or the body of one, addressed by its path with `/body`, and with a hash or without one. A record
//! of a declaration has its address `at` with its current hash, its canonical `text` and, if it has
//! one, the address of its `body`; the record of a body has `at` and `text`.

use serde_json::{Value, json};
use stilt_db::{Database, Program, SourceFile};
use stilt_diag::LineIndex;
use stilt_edit::{Kind, Part, canonical, hash, parts};

use crate::text;

/// A file's text and parts.
#[derive(Debug)]
pub struct FileParts {
    /// The file.
    pub file: SourceFile,
    /// Its text.
    pub text: String,
    /// Its parts (edits.parts), in order.
    pub parts: Vec<Part>,
}

impl FileParts {
    /// The text and parts of `file`.
    pub fn of(db: &Database, program: Program, file: SourceFile) -> Self {
        let text = text(db, file);
        let module = stilt_hir::module_hir(db, program, file).name;
        let found = parts(&module, stilt_db::parse(db, file), &text);
        Self {
            file,
            text,
            parts: found,
        }
    }

    /// The canonical text of part `i` (edits.canonical-text).
    #[must_use]
    pub fn canonical(&self, i: usize) -> String {
        let part = &self.parts[i];
        canonical(part, &self.text[part.extent.clone()])
    }

    /// The hash of part `i` (edits.hash).
    #[must_use]
    pub fn hash(&self, i: usize) -> String {
        hash(&self.canonical(i))
    }

    /// The address of part `i` with its current hash.
    #[must_use]
    pub fn at(&self, i: usize) -> String {
        format!("{}#{}", self.parts[i].address(), self.hash(i))
    }

    /// The index of the declaration that writes its name at `offset`.
    #[must_use]
    pub fn declared_at(&self, offset: usize) -> Option<usize> {
        self.parts
            .iter()
            .position(|p| !p.body && p.name.start == offset)
    }

    /// The index of the body of declaration `decl`, if it has one.
    #[must_use]
    pub fn body_of(&self, decl: usize) -> Option<usize> {
        self.parts.iter().position(|p| p.body && p.decl == decl)
    }

    /// The header of declaration `i` from its name on, on one line: its type parameters, its
    /// parameters, its result and its row, as in `take(self, n: i64) -> List<T>`.
    #[must_use]
    pub fn header(&self, i: usize) -> String {
        let part = &self.parts[i];
        let end = self
            .body_of(i)
            .map_or(part.extent.end, |b| self.parts[b].extent.start);
        let written = self.text[part.name.start..end]
            .split_whitespace()
            .collect::<Vec<_>>();
        written
            .join(" ")
            .replace("( ", "(")
            .replace(", )", ")")
            .replace(" )", ")")
    }

    /// The doc comment of declaration `i` in Markdown, if it has one: its text, then its
    /// examples and properties as code (tests.prop-lines).
    #[must_use]
    pub fn docs(&self, i: usize) -> Option<String> {
        let part = &self.parts[i];
        let lines = self.text[part.extent.clone()]
            .lines()
            .map_while(|l| l.trim_start().strip_prefix("///"));
        docs(lines)
    }

    /// Whether declaration `i` is `pub`.
    #[must_use]
    pub fn is_pub(&self, i: usize) -> bool {
        let part = &self.parts[i];
        self.text[part.extent.clone()]
            .lines()
            .find(|l| !l.trim_start().starts_with("///"))
            .is_some_and(|l| l.trim_start().starts_with("pub "))
    }

    /// The fields that a record of part `i` has beside its other fields: `at`, `text`, and for
    /// a declaration with a body, `body` (edits.showing-parts).
    #[must_use]
    pub fn fields(&self, i: usize) -> [(&'static str, Value); 3] {
        let body = (!self.parts[i].body)
            .then(|| self.body_of(i))
            .flatten()
            .map_or(Value::Null, |b| json!(self.at(b)));
        [
            ("at", json!(self.at(i))),
            ("text", json!(self.canonical(i))),
            ("body", body),
        ]
    }

    /// The record of part `i` that is not a function's: a declaration's, or a body's.
    pub fn record(&self, db: &Database, i: usize) -> Value {
        let part = &self.parts[i];
        let index = LineIndex::new(&self.text);
        let line = index.position(&self.text, offset(part.extent.start)).line;
        let mut record = json!({
            "file": self.file.path(db),
            "line": line,
        });
        record["declaration"] = json!(part.path);
        if !part.body {
            record["kind"] = json!(kind(part.kind));
        }
        for (key, value) in self.fields(i) {
            if !value.is_null() {
                record[key] = value;
            }
        }
        record
    }
}

/// The lines of a doc comment, each without its `///`, in Markdown: its text, then a block of
/// its examples and properties (tests.prop-lines), each as Stilt code.
pub fn docs<'a>(lines: impl Iterator<Item = &'a str>) -> Option<String> {
    let mut text = Vec::new();
    let mut examples = Vec::new();
    for line in lines.map(str::trim) {
        match line
            .strip_prefix("ex:")
            .or_else(|| line.strip_prefix("prop:"))
        {
            Some(code) => examples.push(code.trim()),
            None => text.push(line),
        }
    }
    while text.last().is_some_and(|l| l.is_empty()) {
        text.pop();
    }
    let mut out = text.join("\n");
    if !examples.is_empty() {
        if !out.is_empty() {
            out.push_str("\n\n");
        }
        out.push_str("```stilt\n");
        out.push_str(&examples.join("\n"));
        out.push_str("\n```");
    }
    (!out.is_empty()).then_some(out)
}

fn offset(n: usize) -> stilt_syntax::TextSize {
    stilt_syntax::TextSize::from(u32::try_from(n).unwrap_or(u32::MAX))
}

fn kind(kind: Kind) -> &'static str {
    match kind {
        Kind::Fn => "function",
        Kind::Type => "type",
        Kind::Trait => "trait",
        Kind::Const => "constant",
        Kind::Test => "test",
        Kind::Macro => "macro",
        Kind::Effect => "effect",
    }
}

/// The record of a function, with the fields of its part: `at`, `text` and `body`.
pub fn annotate(record: &mut Value, parts: &FileParts, name_at: usize) {
    let Some(decl) = parts.declared_at(name_at) else {
        return;
    };
    for (key, value) in parts.fields(decl) {
        if !value.is_null() {
            record[key] = value;
        }
    }
}
