//! Where a diagnostic lies among the parts of its file, and its fixes as edits of parts
//! (edits.diagnostic-addresses and edits.fixes-as-edits).

use std::cell::OnceCell;
use std::collections::HashMap;
use std::rc::Rc;

use serde_json::{Value, json};
use stilt_db::{Database, Program, SourceFile};
use stilt_diag::{Diagnostic, Fix};
use stilt_edit::{Part, Replacement, canonical, fix_edits, hash, parts, smallest};

use crate::text;

/// A file's text and parts.
struct Parts {
    text: String,
    parts: Vec<Part>,
}

/// Finds the parts that diagnostics lie in, reading each file's parts once.
pub struct Locator<'a> {
    db: &'a Database,
    program: Program,
    files: HashMap<SourceFile, Rc<Parts>>,
    /// How many parts of the program have each path, once a fix needs it.
    paths: OnceCell<HashMap<String, usize>>,
}

impl std::fmt::Debug for Locator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Locator")
            .field("files", &self.files.len())
            .finish_non_exhaustive()
    }
}

impl<'a> Locator<'a> {
    /// A locator of the program's diagnostics, which reads each file's parts once.
    pub fn new(db: &'a Database, program: Program) -> Self {
        Self {
            db,
            program,
            files: HashMap::new(),
            paths: OnceCell::new(),
        }
    }

    fn parts_of(&mut self, file: SourceFile) -> Rc<Parts> {
        let (db, program) = (self.db, self.program);
        Rc::clone(self.files.entry(file).or_insert_with(|| {
            let text = text(db, file);
            // A manifest has no parts (packages.manifest).
            if file.module_path(db).is_empty() {
                return Rc::new(Parts {
                    text,
                    parts: Vec::new(),
                });
            }
            let module = stilt_hir::module_hir(db, program, file).name;
            let found = parts(&module, stilt_db::parse(db, file), &text);
            Rc::new(Parts { text, parts: found })
        }))
    }

    /// The address, with its hash, of the smallest part that holds the primary span of `d`, if
    /// one does (edits.diagnostic-addresses).
    pub fn at(&mut self, file: SourceFile, d: &Diagnostic) -> Option<String> {
        let of = self.parts_of(file);
        let part = smallest(&of.parts, usize::from(d.range.start()))?;
        let digest = hash(&canonical(part, &of.text[part.extent.clone()]));
        Some(format!("{}#{digest}", part.address()))
    }

    /// The edits of each of the fixes of `d`, as JSON objects (edits.fixes-as-edits).
    pub fn edits(&mut self, file: SourceFile, d: &Diagnostic) -> Vec<Vec<Value>> {
        if d.fixes.is_empty() {
            return Vec::new();
        }
        let of = self.parts_of(file);
        d.fixes.iter().map(|fix| self.fix(&of, fix)).collect()
    }

    fn fix(&mut self, of: &Parts, fix: &Fix) -> Vec<Value> {
        let counts = self.counts();
        let changes: Vec<Replacement> = fix
            .edits
            .iter()
            .map(|e| Replacement {
                range: usize::from(e.range.start())..usize::from(e.range.end()),
                text: e.text.clone(),
            })
            .collect();
        fix_edits(
            &of.text,
            &of.parts,
            |path| counts.get(path).is_some_and(|&n| n > 1),
            &changes,
        )
        .into_iter()
        .map(|e| json!({ "at": e.at, "new": e.new }))
        .collect()
    }

    /// How many declarations of the program have each path.
    fn counts(&mut self) -> HashMap<String, usize> {
        if let Some(counts) = self.paths.get() {
            return counts.clone();
        }
        let mut counts: HashMap<String, usize> = HashMap::new();
        for &file in self.program.files(self.db) {
            for part in self.parts_of(file).parts.iter().filter(|p| !p.body) {
                *counts.entry(part.path.clone()).or_default() += 1;
            }
        }
        self.paths.get_or_init(|| counts).clone()
    }
}
