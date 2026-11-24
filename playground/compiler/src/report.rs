//! What a command prints and how it ends, and the diagnostics of `check`, as `stilt` reports
//! them (`compiler/stilt-cli/src/report.rs`), with the place and the edits of each diagnostic
//! from [`stilt_ide::at`].

use std::io::Write as _;
use std::path::Path;
use std::process::ExitCode;

use serde_json::{Value, json};
use stilt_db::{Database, Program};
use stilt_diag::File;

/// The exit status for a path that isn't a program (conformance.run-statuses).
const NOT_A_PROGRAM: u8 = 2;

/// A command's output on stdout and stderr, and its exit status.
#[derive(Debug, Default)]
pub(crate) struct Report {
    pub(crate) stdout: String,
    pub(crate) stderr: String,
    pub(crate) status: u8,
}

impl Report {
    /// A refusal: a message on stderr, and the status of a path that isn't a program.
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
        eprint!("{}", self.stderr);
        let _ = std::io::stdout().flush();
        ExitCode::from(self.status)
    }
}

/// The report of `f` on the program of one file at `path`, read into a database as `stilt`
/// reads it. A directory is refused: the playground's programs are single files.
pub(crate) fn in_process(path: &str, f: impl FnOnce(&Database, Program) -> Report) -> Report {
    if Path::new(path).is_dir() {
        return Report::refuse(&format!(
            "{path} is a directory, and a program here is one file"
        ));
    }
    let db = Database::default();
    match stilt_db::load(&db, Path::new(path)) {
        Ok(program) => f(&db, program),
        Err(message) => Report::refuse(&message),
    }
}

/// The program's diagnostics: as one JSON object on stdout with `json`
/// (conformance.diagnostic-objects), and otherwise rendered for people on stderr, a blank line
/// between two. The status is 1 when any is an error.
pub(crate) fn check(db: &Database, program: Program, json: bool) -> Report {
    let found = diagnostics(db, program);
    let mut report = Report::default();
    if json {
        report.stdout = format!("{}\n", json!({ "diagnostics": found.entries }));
    } else {
        report.stderr = found.rendered.join("\n");
    }
    report.status = u8::from(found.errors);
    report
}

/// A program's diagnostics, in the order `check` reports them.
pub(crate) struct Diagnostics {
    /// Each as a JSON record.
    pub(crate) entries: Vec<Value>,
    /// Each rendered for people.
    pub(crate) rendered: Vec<String>,
    /// Whether any is an error.
    pub(crate) errors: bool,
}

/// The program's diagnostics, each as its record and rendered. A program of one file has no
/// `docs.lock` (docs.lock-file), so none of its docs is stale, and these are all that `check`
/// reports.
pub(crate) fn diagnostics(db: &Database, program: Program) -> Diagnostics {
    let diagnostics = stilt_rc::check_in_parallel(db, program);
    let mut entries = Vec::new();
    let mut rendered = Vec::new();
    let mut located = stilt_ide::at::Locator::new(db, program);
    for group in diagnostics.chunk_by(|a, b| a.file == b.file) {
        let source = group[0].file;
        let text = text(db, source);
        let file = File::new(source.path(db), &text);
        for d in group.iter().map(|d| &d.diagnostic) {
            let place = located.at(source, d);
            let edits = located.edits(source, d);
            entries.push(file.json(d, place.as_deref(), &edits));
            rendered.push(file.render(d));
        }
    }
    Diagnostics {
        entries,
        rendered,
        errors: diagnostics.iter().any(|d| d.diagnostic.is_error()),
    }
}

pub(crate) use stilt_ide::text;
