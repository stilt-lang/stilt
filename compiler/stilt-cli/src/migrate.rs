//! `stilt migrate`: moves a package to the newest edition (editions.migrate). It checks the
//! package as it is, reads it again with the newest edition's renames, writes each renamed
//! method by its new name and the edition into the manifest, and checks it again.

use std::fmt::Write as _;
use std::path::Path;

use salsa::Setter as _;
use stilt_db::{Database, Program, SourceFile};
use stilt_diag::LineIndex;
use stilt_pkg::edition;
use stilt_syntax::TextRange;

use crate::report::{self, Report};

/// What `stilt migrate PATH` does, as a report.
pub(crate) fn command(path: &Path) -> Report {
    let mut db = Database::default();
    let report = match crate::packages::load(&db, path) {
        Ok(program) => migrate(&mut db, program),
        Err(message) => Report::refuse(&message),
    };
    crate::end(db);
    report
}

fn migrate(db: &mut Database, program: Program) -> Report {
    let root = program.packages(db).list[0].clone();
    let (Some(manifest), Some(dir)) = (root.manifest, root.dir.clone()) else {
        return Report::refuse("a program without stilt.toml is no package, so it has no edition");
    };
    let name = root.name.clone().unwrap_or_else(|| shown_name(&dir));
    let before = report::check(db, program, false);
    if before.status != 0 {
        return before;
    }
    let newest = edition::newest().name;
    if root.edition == newest {
        return printed(format!("{name}: edition {newest}, the newest\n"));
    }
    set_edition(db, program, newest);
    let mut out = String::new();
    let mut rewritten = 0;
    for (file, sites) in renamed(db, program, &root.files) {
        let text = file.bytes(db).clone();
        let shown = String::from_utf8_lossy(&text);
        let lines = LineIndex::new(&shown);
        for (at, to) in &sites {
            let line = lines.position(&shown, at.start()).line;
            let from = &shown[usize::from(at.start())..usize::from(at.end())];
            let _ = writeln!(out, "{}:{line}: {to}, for {from}", file.path(db));
        }
        let new = rewrite(&text, &sites);
        if let Err(e) = std::fs::write(dir.join(file.path(db)), &new) {
            return Report::refuse(&format!("cannot write {}: {e}", file.path(db)));
        }
        file.set_bytes(db).to(new);
        rewritten += 1;
    }
    let bytes = manifest.bytes(db).clone();
    let written = stilt_pkg::manifest::with_edition(&bytes, newest);
    if let Err(e) = std::fs::write(dir.join("stilt.toml"), &written) {
        return Report::refuse(&format!("cannot write stilt.toml: {e}"));
    }
    manifest.set_bytes(db).to(written);
    let files = if rewritten == 1 { "file" } else { "files" };
    let _ = writeln!(
        out,
        "{name}: edition {} → {newest}, {rewritten} {files} rewritten",
        root.edition
    );
    let after = report::check(db, program, false);
    Report {
        stdout: out,
        stderr: after.stderr,
        status: after.status,
    }
}

/// The root package read with `edition`'s renames.
fn set_edition(db: &mut Database, program: Program, name: &'static str) {
    let mut packages = program.packages(db).clone();
    packages.list[0].edition = name;
    program.set_packages(db).to(packages);
}

/// The uses of renamed methods in `files`, each file's in the order of its text, with the
/// name each is written by now.
fn renamed(
    db: &Database,
    program: Program,
    files: &[SourceFile],
) -> Vec<(SourceFile, Vec<(TextRange, &'static str)>)> {
    let mut found = Vec::new();
    for &file in files {
        let starts = stilt_hir::body_starts(db, program, file);
        let mut sites: Vec<(TextRange, &'static str)> = (0..starts.len())
            .flat_map(|i| {
                let index = u32::try_from(i).expect("under 4G bodies");
                let body = &stilt_types::infer_body(db, program, file, index).body;
                body.renamed
                    .iter()
                    .map(move |(at, to)| (*at + starts[i], *to))
            })
            .collect();
        sites.sort_by_key(|(at, _)| at.start());
        sites.dedup();
        if !sites.is_empty() {
            found.push((file, sites));
        }
    }
    found
}

/// `text` with each site written by its new name, the later first so that offsets hold.
fn rewrite(text: &[u8], sites: &[(TextRange, &str)]) -> Vec<u8> {
    let mut out = text.to_vec();
    for (at, to) in sites.iter().rev() {
        out.splice(usize::from(at.start())..usize::from(at.end()), to.bytes());
    }
    out
}

fn printed(stdout: String) -> Report {
    Report {
        stdout,
        ..Report::default()
    }
}

/// A package's name as its directory gives it, for a manifest without one.
fn shown_name(dir: &Path) -> String {
    dir.canonicalize()
        .ok()
        .and_then(|d| d.file_name().map(|n| n.to_string_lossy().into_owned()))
        .unwrap_or_else(|| ".".to_owned())
}

#[cfg(test)]
mod tests;
