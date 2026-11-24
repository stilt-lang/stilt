//! The declarations of the program's and the standard library's files by their paths
//! (edits.paths), each file's parts read once, for what a hole's context and a hover show
//! of a declaration the code names: a type's definition, and a function's header.

use std::collections::HashMap;
use std::rc::Rc;

use stilt_db::{Database, Program, SourceFile};
use stilt_types::holes::Fit;

use super::parts::FileParts;

/// The parts of the program's and the standard library's files, read once each.
pub struct Parts<'a> {
    db: &'a Database,
    program: Program,
    files: HashMap<SourceFile, Rc<FileParts>>,
}

impl std::fmt::Debug for Parts<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Parts")
            .field("files", &self.files.len())
            .finish_non_exhaustive()
    }
}

impl<'a> Parts<'a> {
    /// The parts of `program`'s files, none read yet.
    pub fn new(db: &'a Database, program: Program) -> Self {
        Self {
            db,
            program,
            files: HashMap::new(),
        }
    }

    /// The declaration whose path is `path`, with its file's parts.
    pub fn declaration(&mut self, path: &str) -> Option<(Rc<FileParts>, usize)> {
        let (db, program) = (self.db, self.program);
        for &file in program.files(db).iter().chain(program.std(db)) {
            let module = stilt_hir::module_hir(db, program, file).name;
            if !path.starts_with(&format!("{module}.")) {
                continue;
            }
            let of = Rc::clone(
                self.files
                    .entry(file)
                    .or_insert_with(|| Rc::new(FileParts::of(db, program, file))),
            );
            if let Some(i) = of.parts.iter().position(|p| !p.body && p.path == path) {
                return Some((of, i));
            }
        }
        None
    }

    /// A type's declaration as `stilt fmt` writes it, without its doc comments.
    pub fn definition(&mut self, path: &str) -> Option<String> {
        let (of, i) = self.declaration(path)?;
        let text = of.canonical(i);
        let lines: Vec<&str> = text
            .lines()
            .skip_while(|l| l.trim_start().starts_with("///"))
            .collect();
        Some(lines.join("\n"))
    }

    /// A function's header, as code calls it: its qualifier, its name, its type parameters, its
    /// parameters, its result and its row, on one line, as in
    /// `List.take(self, n: i64) -> List<T>`.
    pub fn header(&mut self, fit: &Fit) -> Option<String> {
        let (of, i) = self.declaration(&fit.path)?;
        let signature = of.header(i);
        Some(match &fit.qualifier {
            Some(q) => format!("{q}.{signature}"),
            None => signature,
        })
    }
}
