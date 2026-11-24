//! Profiles (builds.profiles):
//! the counts that `stilt run --profile` and `stilt test --profile` take as the program runs
//! in its debug build, kept as text beside the program, and read by its release builds.
//!
//! A program's profile is `default.profile` inside a directory program or beside a package's
//! manifest, and `NAME.profile` beside a program of one file `NAME.lt`. At the end of a
//! profiled run, each count is added to it ([`add`]), but for a run that ends with status 134,
//! whose process ends before it can write. A release build reads it ([`read`]) and drops each
//! line whose body changed since ([`split`]), which the performance report lists; the others
//! tell clang which branches are likely and which functions are hot and which cold
//! ([`hints`]). A line that isn't of the form is E0610, which names it.

mod lines;
mod places;
#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use stilt_db::{Database, Program};
use stilt_diag::{Diagnostic, File, codes};
use stilt_syntax::{TextRange, TextSize};

pub(crate) use lines::{Kind, Line};
pub(crate) use places::Bodies;

use crate::report::Report;

/// The profile of the program at `path`.
pub(crate) fn path_of(program: &Path) -> PathBuf {
    if program.is_dir() {
        program.join("default.profile")
    } else {
        program.with_extension("profile")
    }
}

/// The program's profile as its reports name it: relative to the program's root, as its files
/// are.
fn shown(program: &Path) -> String {
    let path = path_of(program);
    let name = path.file_name().unwrap_or_default();
    name.to_string_lossy().into_owned()
}

/// The lines of the program's profile, none when it has none, or the report of E0610 at its
/// first line that isn't of the form.
pub(crate) fn read(program: &Path) -> Result<Vec<Line>, Report> {
    let Ok(text) = std::fs::read_to_string(path_of(program)) else {
        return Ok(Vec::new());
    };
    lines::parse(&text).map_err(|m| Report {
        stderr: format!("{}\n", malformed(program, &text, &m)),
        status: crate::NOT_A_PROGRAM,
        ..Report::default()
    })
}

/// The report of `check` on the program at `path`, with E0610 when a line of the program's
/// profile isn't of its form: after the program's diagnostics, rendered for people or, with
/// `json`, among the records of the object, and with the status of a program with errors.
pub(crate) fn checked(path: &Path, mut report: Report, json: bool) -> Report {
    let Ok(text) = std::fs::read_to_string(path_of(path)) else {
        return report;
    };
    let Err(m) = lines::parse(&text) else {
        return report;
    };
    let name = shown(path);
    let file = File::new(&name, &text);
    if json {
        let mut object: serde_json::Value =
            serde_json::from_str(&report.stdout).unwrap_or_else(|_| serde_json::json!({}));
        if let Some(found) = object["diagnostics"].as_array_mut() {
            found.push(file.json(&error(&m), None, &[]));
        }
        report.stdout = format!("{object}\n");
    } else {
        if !report.stderr.is_empty() {
            report.stderr.push('\n');
        }
        report.stderr.push_str(&file.render(&error(&m)));
    }
    report.status = report.status.max(1);
    report
}

fn error(m: &lines::Malformed) -> Diagnostic {
    let at = |n: usize| TextSize::from(u32::try_from(n).unwrap_or(u32::MAX));
    let range = TextRange::new(at(m.range.start), at(m.range.end));
    let message = format!(
        "line {} of the profile isn't of its form: {}",
        m.number, m.reason
    );
    Diagnostic::new(codes::E0610, range, message)
}

/// The rendering of E0610 at a line of the program's profile.
fn malformed(program: &Path, text: &str, m: &lines::Malformed) -> String {
    let name = shown(program);
    File::new(&name, text).render(&error(m))
}

/// Adds a profiled run's counts to the program's profile, each place in the body of the
/// program that holds it, and writes it, sorted.
pub(crate) fn add(
    path: &Path,
    db: &Database,
    program: Program,
    counted: &[(stilt_runtime::profile::Counted, u64)],
) -> Result<(), Report> {
    let old = read(path)?;
    let new = Bodies::of(db, program).lines(counted);
    let text = lines::render(&lines::merge(old, new));
    let file = path_of(path);
    std::fs::write(&file, text)
        .map_err(|e| Report::refuse(&format!("cannot write {}: {e}", file.display())))
}

/// The lines of a profile whose bodies are as they were when they were counted, and those whose
/// bodies changed, or are gone, since: the hash of the body at each line's address isn't the
/// line's.
pub(crate) fn split(lines: Vec<Line>, bodies: &Bodies) -> (Vec<Line>, Vec<Line>) {
    lines
        .into_iter()
        .partition(|l| bodies.at(&l.address).is_some_and(|b| b.hash == l.hash))
}

/// The hints that the lines of a profile whose bodies are as they were give a release build:
/// the count of each mark of the code, by what it marks and its location word, and the entry
/// of each body the profile counts, whose marks without a count were never reached.
pub(crate) fn hints(valid: &[Line], bodies: &Bodies) -> stilt_codegen_c::Hints {
    let mut counts = HashMap::new();
    let mut profiled = HashSet::new();
    for line in valid {
        let Some(body) = bodies.at(&line.address) else {
            continue;
        };
        profiled.insert(body.entry());
        let word = match line.kind {
            Kind::Entry => body.entry(),
            _ => body.word(line.place.0, line.place.1),
        };
        if let Some(counted) = places::counted(line.kind) {
            counts.insert((counted, word), line.count);
        }
    }
    stilt_codegen_c::Hints { counts, profiled }
}
