//! Pinned docs (docs.pins, docs.stale and docs.writing-pins): `check` and `test` report each stale
//! doc as W0002, from the `docs.lock` of its package, and the commands that write source pin docs
//! ([`pin`]).

mod pin;

use std::collections::HashMap;

use stilt_db::{Database, PackageInfo, Program, SourceFile};
use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_edit::{Doc, Pin, docs, is_stale, parts, read_lock};
use stilt_hir::FileDiagnostic;
use stilt_syntax::{TextRange, TextSize};

pub(crate) use pin::{before, pin};

use crate::report::text;

/// The W0002 of the program's stale docs (docs.stale), none when a file has a syntax error, as
/// errors.syntax-errors reports only syntax errors then.
pub(crate) fn stale(db: &Database, program: Program) -> Vec<FileDiagnostic> {
    let files = program.files(db);
    if files
        .iter()
        .any(|&f| stilt_db::syntax_error(db, f).is_some())
    {
        return Vec::new();
    }
    let mut found = Vec::new();
    for package in &program.packages(db).list {
        let Some(lock) = package.pins else {
            continue;
        };
        let pins = read_lock(&String::from_utf8_lossy(lock.bytes(db)));
        if pins.is_empty() {
            continue;
        }
        let by_path: HashMap<&str, &Pin> = pins.iter().map(|p| (p.path.as_str(), p)).collect();
        for (file, doc) in package_docs(db, package) {
            if by_path
                .get(doc.path.as_str())
                .is_some_and(|pin| is_stale(&doc, pin))
            {
                found.push(FileDiagnostic {
                    file,
                    diagnostic: warning(&text(db, file), &doc),
                });
            }
        }
    }
    found
}

/// The docs of a package's files that can be pinned: each of a declaration whose path names it
/// alone (docs.pins), with the module names the package gives its modules (docs.lock-file).
fn package_docs(db: &Database, package: &PackageInfo) -> Vec<(SourceFile, Doc)> {
    let mut all = Vec::new();
    let mut paths: HashMap<String, usize> = HashMap::new();
    for &file in &package.files {
        let text = text(db, file);
        let module = local(package.prefix.as_deref(), file.module_path(db));
        let parse = stilt_db::parse(db, file);
        for part in parts(&module, parse, &text).into_iter().filter(|p| !p.body) {
            *paths.entry(part.path).or_default() += 1;
        }
        all.extend(docs(&module, parse, &text).into_iter().map(|d| (file, d)));
    }
    all.retain(|(_, d)| paths.get(&d.path) == Some(&1));
    all
}

/// A module's name in its package, without the first segment that a dependency's modules take
/// in the program (packages.modules-of-dependencies).
fn local(prefix: Option<&str>, path: &[String]) -> String {
    match (prefix, path) {
        (Some(_), [_]) => "main".to_owned(),
        (Some(_), [_, rest @ ..]) => rest.join("."),
        _ => path.join("."),
    }
}

/// The W0002 of a stale doc, whose fix sends its declaration back as it is (docs.stale).
fn warning(text: &str, doc: &Doc) -> Diagnostic {
    let offset = |n: usize| TextSize::try_from(n).unwrap_or_default();
    let range = TextRange::new(offset(doc.first.start), offset(doc.first.end));
    let first = text.get(doc.first.clone()).unwrap_or_default();
    Diagnostic::new(
        codes::W0002,
        range,
        format!(
            "the signature of `{}` changed after this doc was written",
            doc.path
        ),
    )
    .with_fix(Fix::new(
        "if the doc still holds, send the declaration back as it is, which pins the doc again",
        vec![Edit::replace(range, first)],
    ))
}
