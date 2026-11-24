//! Fetched dependencies with errors (packages.dependencies-with-errors): a fetched package is
//! checked with the program, but its diagnostics, of its code and of its manifest, aren't reported.
//! Each fetched package that has an error gives the program one E0607, at the first entry of the
//! root's manifest through which it arrives.

use std::collections::VecDeque;

use stilt_db::{Db, Program, SourceFile};
use stilt_diag::{Diagnostic, File, codes};
use stilt_hir::FileDiagnostic;
use stilt_syntax::TextSize;

use crate::queries::{body_count, body_diagnostics};

/// The E0607 of each fetched package with an error.
pub(super) fn errors(db: &dyn Db, program: Program) -> Vec<FileDiagnostic> {
    let packages = program.packages(db);
    let Some(root) = packages.root() else {
        return Vec::new();
    };
    let Some(manifest) = root.manifest else {
        return Vec::new();
    };
    let mut found = Vec::new();
    for (i, package) in packages.list.iter().enumerate() {
        if !package.fetched {
            continue;
        }
        let Some((code, place)) = first_error(db, program, i) else {
            continue;
        };
        let Some(entry) = arrival(program.packages(db), i) else {
            continue;
        };
        let name = package.name.as_deref().unwrap_or("?");
        let version = package.version.as_deref().unwrap_or("?");
        let message = format!("`{name}` {version} has errors, the first an {code} at {place}");
        found.push(FileDiagnostic {
            file: manifest,
            diagnostic: Diagnostic::new(codes::E0607, root.deps[entry].key, message),
        });
    }
    found
}

/// The first entry of the root's manifest through whose packages `target` arrives.
fn arrival(packages: &stilt_db::Packages, target: usize) -> Option<usize> {
    let root = packages.root()?;
    root.deps.iter().position(|dep| {
        let mut queue: VecDeque<usize> = dep.package.into_iter().collect();
        let mut seen = vec![false; packages.list.len()];
        while let Some(p) = queue.pop_front() {
            if p == target {
                return true;
            }
            if std::mem::replace(&mut seen[p], true) {
                continue;
            }
            queue.extend(packages.list[p].deps.iter().filter_map(|d| d.package));
        }
        false
    })
}

/// The code and place of the first error of a fetched package: of its manifest, then of its
/// files in the order of their paths, as `name/path:line:col`.
fn first_error(db: &dyn Db, program: Program, package: usize) -> Option<(String, String)> {
    let info = &program.packages(db).list[package];
    let name = info.name.as_deref().unwrap_or("?");
    let placed = |file: SourceFile, at: TextSize| {
        let text = String::from_utf8_lossy(file.bytes(db)).into_owned();
        let path = file.path(db);
        let within = path
            .split_once("/src/")
            .map_or(path.as_str(), |(_, rest)| rest);
        let position = File::new(path, &text).position(at);
        format!("{name}/src/{within}:{position}")
    };
    if let Some(manifest) = info.manifest {
        let read = stilt_pkg::manifest::read(manifest.bytes(db));
        let ungranted = info.deps.iter().find_map(|dep| {
            super::ungranted_entries(db, program, dep)
                .into_iter()
                .next()
        });
        if let Some(d) = read.problems.first().or(ungranted.as_ref()) {
            let text = String::from_utf8_lossy(manifest.bytes(db)).into_owned();
            let position = File::new("stilt.toml", &text).position(d.range.start());
            return Some((d.code.to_string(), format!("{name}/stilt.toml:{position}")));
        }
    }
    if let Some((file, d)) = info
        .files
        .iter()
        .find_map(|&f| Some((f, stilt_db::syntax_error(db, f).clone()?)))
    {
        return Some((d.code.to_string(), placed(file, d.range.start())));
    }
    for &file in &info.files {
        let mut errors: Vec<(TextSize, Diagnostic)> =
            stilt_hir::file_diagnostics(db, program, file)
                .iter()
                .filter(|d| d.is_error())
                .map(|d| (d.range.start(), d.clone()))
                .collect();
        let starts = stilt_hir::body_starts(db, program, file);
        for index in 0..body_count(db, program, file) {
            let start = starts[index as usize];
            errors.extend(
                body_diagnostics(db, program, file, index)
                    .iter()
                    .filter(|d| d.is_error())
                    .map(|d| (d.range.start() + start, d.clone())),
            );
        }
        if let Some((at, d)) = errors.into_iter().min_by_key(|(at, _)| *at) {
            return Some((d.code.to_string(), placed(file, at)));
        }
    }
    None
}
