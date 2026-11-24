//! Approving drafts of conformance tests.
//!
//! A draft is a test under a `_pending/` directory. It may be approved once every ID it cites
//! is a paragraph of the Reference, since a conformance test checks only what the Reference
//! states. Approving moves it to the same path without the `_pending/` component, where the
//! runner finds it (conformance.location).

use std::ffi::OsStr;
use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::{Component, Path, PathBuf};

use crate::annotations;
use crate::coverage::Paragraphs;
use crate::discovery::Test;

/// The name of the directory that holds drafts.
const PENDING: &str = "_pending";

/// Approves every draft among `tests` that may be approved, and returns the report: a line
/// for each draft held back, with the reason, and a summary. The flag tells whether every
/// draft was approved.
pub(crate) fn approve(paragraphs: &Paragraphs, tests: &[Test]) -> Result<(String, bool), String> {
    let mut report = String::new();
    let mut approved = 0;
    for test in tests {
        let source = location(test);
        match review(paragraphs, test, &source) {
            Ok(destination) => {
                move_draft(&source, &destination)
                    .map_err(|error| format!("cannot move {}: {error}", test.name))?;
                approved += 1;
            }
            Err(reason) => {
                let _ = writeln!(report, "HELD {}: {reason}", test.name);
            }
        }
    }
    let held = tests.len() - approved;
    let _ = writeln!(
        report,
        "{} drafts: {approved} approved, {held} held",
        tests.len()
    );
    Ok((report, held == 0))
}

/// Where the draft goes once approved, or why it may not be approved yet.
fn review(paragraphs: &Paragraphs, test: &Test, source: &Path) -> Result<PathBuf, String> {
    let destination =
        destination(source).ok_or_else(|| format!("it isn't under a `{PENDING}/` directory"))?;
    let spec = annotations::parse(&test.files, &test.header_file)
        .map_err(|malformed| malformed.to_string())?;
    if spec.rules.is_empty() {
        return Err("it cites no paragraph".to_owned());
    }
    if let Some(id) = spec.rules.iter().find(|id| !paragraphs.defines(id)) {
        return Err(format!(
            "it cites `{id}`, which no paragraph of the Reference has"
        ));
    }
    if destination.exists() {
        return Err(format!("{} already exists", destination.display()));
    }
    Ok(destination)
}

/// The test's file, or the directory of a directory test.
fn location(test: &Test) -> PathBuf {
    // Joining the target `.` of a directory test leaves a trailing `.`, which `components`
    // drops.
    test.dir.join(&test.target).components().collect()
}

/// `path` without its first `_pending` component, or `None` if it has none.
fn destination(path: &Path) -> Option<PathBuf> {
    let mut found = false;
    let kept: PathBuf = path
        .components()
        .filter(|component| {
            let pending = !found && *component == Component::Normal(OsStr::new(PENDING));
            found |= pending;
            !pending
        })
        .collect();
    found.then_some(kept)
}

/// Moves a draft to its destination, then removes the directories under `_pending/` that the
/// move leaves empty.
fn move_draft(source: &Path, destination: &Path) -> io::Result<()> {
    if let Some(parent) = destination.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::rename(source, destination)?;
    let mut dir = source.parent();
    while let Some(current) = dir {
        if current.file_name() == Some(OsStr::new(PENDING)) || !is_empty(current)? {
            break;
        }
        fs::remove_dir(current)?;
        dir = current.parent();
    }
    Ok(())
}

fn is_empty(dir: &Path) -> io::Result<bool> {
    Ok(fs::read_dir(dir)?.next().is_none())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_draft_moves_out_of_its_first_pending_directory() {
        assert_eq!(
            destination(Path::new("conformance/_pending/lexical/a.lt")),
            Some(PathBuf::from("conformance/lexical/a.lt"))
        );
        assert_eq!(
            destination(Path::new("_pending/x/_pending/y")),
            Some(PathBuf::from("x/_pending/y"))
        );
        assert_eq!(destination(Path::new("conformance/lexical/a.lt")), None);
        assert_eq!(destination(Path::new("tests/_pending_old/a.lt")), None);
    }

    #[test]
    fn a_directory_test_is_located_by_its_directory() {
        let test = Test {
            name: "t/_pending/cycle".to_owned(),
            dir: PathBuf::from("t/_pending/cycle"),
            target: ".".to_owned(),
            header_file: "main.lt".to_owned(),
            files: Vec::new(),
        };
        assert_eq!(location(&test), PathBuf::from("t/_pending/cycle"));
    }
}
