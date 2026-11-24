//! The editor's answers (goal one-engine): what the language server tells an editor about a
//! program, from its database. Each reads the program as the engine holds it, the text of the
//! editor's open buffers in place of their files', and returns the values of [`stilt_lsp`]'s
//! protocol: diagnostics with their fixes, hover, definitions and type definitions, completion
//! and members, signatures, references and renames, the outline and the program's symbols,
//! inlay hints, semantic tokens, highlights, code lenses, and where a position is.
//!
//! What needs only a file's text, its folding and selection ranges, its outline and its
//! formatting, needs no program ([`syntax`], [`outline`]).

// The syntax tree's kinds read as the grammar names them, as in the parser and the formatter.
#![allow(clippy::enum_glob_use)]

pub mod access;
mod complete;
mod hints;
pub mod lenses;
mod members;
pub mod outline;
pub mod references;
mod scope;
pub mod signature;
mod snippets;
pub mod syntax;
mod tokens;
mod typed;
pub(crate) mod words;

use std::path::PathBuf;

use stilt_db::{Database, Program, SourceFile};
use stilt_lsp::{Diagnostic, Edit, FileDiagnostics, Fix, Note, Place, Whereabouts};
use stilt_types::position::{Named, named_at};

use crate::show::lookup::Parts;
use crate::show::parts::FileParts;
use crate::show::position::resolve_written;

pub use complete::{Completed, completion, members};
pub use hints::hints;
pub use outline::program_symbols;
pub use tokens::tokens;

/// Each file of the program with its canonical path.
pub type Paths = [(SourceFile, PathBuf)];

/// Where the type of what the code names at `offset` is declared: a variable's or a field's
/// type, or the type a variant is of.
pub fn type_definition(
    db: &Database,
    program: Program,
    paths: &Paths,
    file: SourceFile,
    offset: u32,
) -> Option<Place> {
    let mut parts = Parts::new(db, program);
    let path = match named_at(db, program, file, offset.into())? {
        Named::Local { ty, .. } | Named::Field { ty, .. } => {
            let head = ty.split(['<', ' ']).next()?.to_owned();
            resolve_written(db, program, file, &head, &mut parts)?
        }
        Named::Variant(path) | Named::Operation { effect: path, .. } => path,
        Named::Function(_) => return None,
    };
    let (of, i) = parts.declaration(&path)?;
    let (_, at) = paths.iter().find(|(f, _)| *f == of.file)?;
    let name = &of.parts[i].name;
    Some(Place {
        path: at.clone(),
        start: u32::try_from(name.start).ok()?,
        end: u32::try_from(name.end).ok()?,
    })
}

/// The module of `file`, with its tier, and the function whose declaration or body holds
/// `offset`, by its address.
pub fn whereabouts(db: &Database, program: Program, file: SourceFile, offset: u32) -> Whereabouts {
    let module = stilt_hir::module_hir(db, program, file).name.to_string();
    let tier = stilt_types::facts::tier(db, program, file).to_owned();
    let of = FileParts::of(db, program, file);
    let at = offset as usize;
    let function = (of.parts.iter())
        .filter(|p| p.extent.start <= at && at <= p.extent.end)
        .map(|p| &of.parts[p.decl])
        .filter(|d| d.kind == stilt_edit::Kind::Fn)
        .min_by_key(|d| d.extent.len())
        .map(|d| d.path.clone());
    Whereabouts {
        module,
        tier,
        function,
    }
}

/// The diagnostics of every file of the program that has any, as `check` finds them, each
/// with its fixes as edits of its file (goal one-diagnostic-shape), and its notes.
pub fn diagnostics(
    db: &Database,
    program: Program,
    paths: &[(SourceFile, PathBuf)],
) -> Vec<FileDiagnostics> {
    let found = stilt_rc::check_in_parallel(db, program);
    let mut files: Vec<FileDiagnostics> = Vec::new();
    for group in found.chunk_by(|a, b| a.file == b.file) {
        let Some((_, path)) = paths.iter().find(|(f, _)| *f == group[0].file) else {
            continue;
        };
        let diagnostics = group.iter().map(|d| diagnostic(&d.diagnostic)).collect();
        files.push(FileDiagnostics {
            path: path.clone(),
            diagnostics,
        });
    }
    files
}

fn diagnostic(d: &stilt_diag::Diagnostic) -> Diagnostic {
    let fixes = d
        .fixes
        .iter()
        .map(|f| Fix {
            title: f.title.clone(),
            edits: (f.edits.iter())
                .map(|e| Edit {
                    start: e.range.start().into(),
                    end: e.range.end().into(),
                    text: e.text.clone(),
                })
                .collect(),
        })
        .collect();
    let notes = (d.notes.iter())
        .map(|n| Note {
            start: n.range.start().into(),
            end: n.range.end().into(),
            text: n.text.clone(),
        })
        .collect();
    Diagnostic {
        start: d.range.start().into(),
        end: d.range.end().into(),
        error: d.is_error(),
        code: d.code.as_str().to_owned(),
        message: d.message.clone(),
        fixes,
        notes,
    }
}
