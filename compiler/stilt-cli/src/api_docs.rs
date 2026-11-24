//! `stilt doc`: the documentation of a package's API, or of the standard library's, as HTML
//! pages or one JSON object (docs.stilt-doc, docs.module-pages and docs.std). Each module of the
//! root package has a page, which shows its description and its `pub` declarations, each with its
//! signature, its doc and, for a function, the limitable facts that the package's API holds.

mod html;
mod markdown;
mod model;

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use stilt_db::{Database, Program};
use stilt_diag::File;

use crate::report::{Report, text};

pub(crate) use model::{Item, Module, Package};

/// What `stilt doc` does: the pages of the standard library with `std`, and otherwise those of
/// the package at `path`.
pub(crate) fn command(path: &Path, out: Option<&Path>, json: bool, std: bool) -> ExitCode {
    if std {
        standard_library(out, json).print()
    } else {
        package(path, out, json).print()
    }
}

/// What `stilt doc PATH [-o DIR] [--json]` does: the pages of the package at `path`, written
/// into `out` or into `doc` at the package's root, or printed as JSON. A program with an error is
/// refused with its first error.
fn package(path: &Path, out: Option<&Path>, json: bool) -> Report {
    let db = Database::default();
    let program = match crate::packages::load(&db, path) {
        Ok(program) => program,
        Err(message) => return Report::refuse(&message),
    };
    let report = if let Some(error) = first_error(&db, program) {
        Report::refuse(&format!("{} has an error: {error}", path.display()))
    } else {
        let package = model::package(&db, program, &name(&db, program, path));
        let dir = out.map_or_else(|| root(path).join("doc"), Path::to_path_buf);
        delivered(&package, json, &dir)
    };
    crate::end(db);
    report
}

/// What `stilt doc --std [-o DIR] [--json]` does: the pages of the standard library, with its
/// examples, written into `out` or into `doc` in the working directory, or printed as JSON
/// (docs.std).
fn standard_library(out: Option<&Path>, json: bool) -> Report {
    stilt_db::read_std_examples();
    let db = Database::default();
    let program = stilt_db::program(&db, Vec::new());
    let package = model::standard_library(&db, program);
    let report = delivered(&package, json, out.unwrap_or(Path::new("doc")));
    crate::end(db);
    report
}

/// The package's pages printed as JSON, or written into `dir`.
fn delivered(package: &Package, json: bool, dir: &Path) -> Report {
    if json {
        Report {
            stdout: format!("{}\n", model::json(package)),
            ..Report::default()
        }
    } else {
        written(package, dir)
    }
}

/// The code and place of the program's first error, as `E0311 at main.lt:3:5`.
fn first_error(db: &Database, program: Program) -> Option<String> {
    let diagnostics = stilt_rc::check_in_parallel(db, program);
    let d = diagnostics.iter().find(|d| d.diagnostic.is_error())?;
    let source = text(db, d.file);
    let position = File::new(d.file.path(db), &source).position(d.diagnostic.range.start());
    Some(format!(
        "{} at {}:{position}",
        d.diagnostic.code,
        d.file.path(db)
    ))
}

/// The package's name: its manifest's, or for a program without one, its directory's name or
/// its file's name without `.lt` (docs.stilt-doc).
fn name(db: &Database, program: Program, path: &Path) -> String {
    let declared = (program.packages(db).root()).and_then(|root| root.name.clone());
    declared.unwrap_or_else(|| {
        let full = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
        let stem = if full.is_file() {
            full.file_stem()
        } else {
            full.file_name()
        };
        stem.map_or_else(|| "main".to_owned(), |s| s.to_string_lossy().into_owned())
    })
}

/// The package's root: the directory of its manifest or the directory program, or a file
/// program's directory.
fn root(path: &Path) -> PathBuf {
    if path.is_file() {
        path.parent()
            .map_or_else(|| PathBuf::from("."), Path::to_path_buf)
    } else {
        path.to_path_buf()
    }
}

/// Writes the package's pages into `dir`, and reports the path of its index.
fn written(package: &Package, dir: &Path) -> Report {
    let mut files = vec![
        ("index.html".to_owned(), html::index(package)),
        ("style.css".to_owned(), html::STYLE.to_owned()),
    ];
    for module in &package.modules {
        files.push((
            format!("{}.html", module.address),
            html::module(package, module),
        ));
    }
    let wrote = std::fs::create_dir_all(dir).and_then(|()| {
        files
            .iter()
            .try_for_each(|(name, text)| std::fs::write(dir.join(name), text))
    });
    match wrote {
        Ok(()) => Report {
            stdout: format!("{}\n", dir.join("index.html").display()),
            ..Report::default()
        },
        Err(e) => Report::refuse(&format!("can't write {}: {e}", dir.display())),
    }
}
