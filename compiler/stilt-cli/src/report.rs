//! What a command prints and how it ends, whether it ran in this process or in the engine,
//! which answers with the report this process would have printed (goal one-engine).

use std::io::Write as _;
use std::path::Path;
use std::process::ExitCode;

use serde::{Deserialize, Serialize};
use serde_json::json;
use stilt_db::{Database, Program};
use stilt_diag::File;
use stilt_hir::FileDiagnostic;

use crate::NOT_A_PROGRAM;

/// A command's output on stdout and stderr, and its exit status.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Report {
    pub(crate) stdout: String,
    pub(crate) stderr: String,
    pub(crate) status: u8,
}

impl Report {
    /// A refusal: a message on stderr, and the status of a path that isn't a program
    /// (conformance.run-statuses).
    pub(crate) fn refuse(message: &str) -> Self {
        Self {
            stderr: format!("stilt: {message}\n"),
            status: NOT_A_PROGRAM,
            ..Self::default()
        }
    }

    /// Prints the report, and ends as it does.
    pub(crate) fn print(&self) -> ExitCode {
        print!("{}", self.stdout);
        eprint!("{}", crate::colour::stderr(&self.stderr));
        let _ = std::io::stdout().flush();
        ExitCode::from(self.status)
    }
}

/// The report of `f` on the program at `path`, read into a database of this process.
pub(crate) fn in_process(path: &Path, f: impl FnOnce(&Database, Program) -> Report) -> Report {
    let db = Database::default();
    let report = match crate::packages::load(&db, path) {
        Ok(program) => f(&db, program),
        Err(message) => Report::refuse(&message),
    };
    crate::end(db);
    report
}

/// The program's diagnostics: as one JSON object on stdout with `json`
/// (conformance.diagnostic-objects), and otherwise rendered for people on stderr, a blank line
/// between two. The status is 1 when any is an error.
pub(crate) fn check(db: &Database, program: Program, json: bool) -> Report {
    let found = diagnostics(db, program, json);
    let mut report = Report::default();
    if json {
        report.stdout = format!("{}\n", json!({ "diagnostics": found.entries }));
    } else {
        report.stderr = found.rendered;
    }
    report.status = u8::from(found.errors);
    report
}

/// A program's diagnostics, as `check` reports them.
pub(crate) struct Diagnostics {
    /// Each as a JSON record, with `json`.
    pub(crate) entries: Vec<serde_json::Value>,
    /// Each rendered for people, a blank line between two, without `json`.
    pub(crate) rendered: String,
    /// Whether any is an error.
    pub(crate) errors: bool,
}

/// The program's diagnostics, its stale docs among them (docs.stale): as JSON records with
/// `json`, and otherwise rendered for people.
pub(crate) fn diagnostics(db: &Database, program: Program, json: bool) -> Diagnostics {
    let mut diagnostics = stilt_rc::check_in_parallel(db, program);
    let stale = crate::docs::stale(db, program);
    if !stale.is_empty() {
        diagnostics.extend(stale);
        diagnostics.sort_by(|a, b| {
            let key = |d: &FileDiagnostic| {
                (
                    d.file.path(db),
                    d.diagnostic.range.start(),
                    d.diagnostic.code,
                )
            };
            key(a).cmp(&key(b))
        });
    }
    let mut entries = Vec::new();
    let mut rendered = Vec::new();
    let mut located = stilt_ide::at::Locator::new(db, program);
    for group in diagnostics.chunk_by(|a, b| a.file == b.file) {
        let source = group[0].file;
        let text = text(db, source);
        let file = File::new(source.path(db), &text);
        for d in group.iter().map(|d| &d.diagnostic) {
            if json {
                let place = located.at(source, d);
                let edits = located.edits(source, d);
                entries.push(file.json(d, place.as_deref(), &edits));
            } else {
                rendered.push(file.render(d));
            }
        }
    }
    Diagnostics {
        entries,
        rendered: rendered.join("\n"),
        errors: diagnostics.iter().any(|d| d.diagnostic.is_error()),
    }
}

pub(crate) use stilt_ide::text;
