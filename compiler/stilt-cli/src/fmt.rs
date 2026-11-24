//! `stilt fmt`: writes source files in the canonical format (syntax.format and syntax.no-options;
//! Inferred facts, "Seven commands").
//!
//! It formats a file, or every `.lt` file under a directory, skipping the entries whose names
//! start with `.`, in place, then pins the docs of the package that the path lies in, if it lies
//! in one (docs.writing-pins). It prints the path of each file it rewrote, and reports each file
//! with a syntax error, which it leaves as it is. It exits with status 0 when every file was
//! already canonical, so that a check fails on code that isn't, and 1 otherwise. The command has
//! no flags, as the formatter has no options: a check is a run that rewrites nothing.

use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use stilt_diag::File;
use stilt_fmt::Error;

/// What formatting one file did.
enum Outcome {
    Canonical,
    Rewritten,
    Refused,
}

/// Formats the file or the files under the directory at `path`.
pub(crate) fn command(path: &Path) -> ExitCode {
    let files = match sources(path) {
        Ok(files) => files,
        Err(error) => {
            eprintln!("{}: {error}", path.display());
            return ExitCode::from(crate::NOT_A_PROGRAM);
        }
    };
    // Files are formatted across the machine's cores, and reported in order of path.
    let outcomes = stilt_db::parallel::map(files, |file| {
        let (outcome, message) = format_file(&file);
        (file, outcome, message)
    });
    let mut canonical = true;
    for (file, outcome, message) in outcomes {
        if let Some(message) = message {
            eprint!("{message}");
        }
        match outcome {
            Outcome::Canonical => {}
            Outcome::Rewritten => {
                println!("{}", file.display());
                canonical = false;
            }
            Outcome::Refused => canonical = false,
        }
    }
    if let Some(package) = package_of(path)
        && let Err(message) = crate::docs::pin(&package, &BTreeSet::from([0]), &[])
    {
        eprintln!("{message}");
        canonical = false;
    }
    if canonical {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// The package that `path` lies in, whose docs `fmt` pins (docs.writing-pins): the nearest
/// directory with a manifest, `path` itself or one that holds it.
fn package_of(path: &Path) -> Option<PathBuf> {
    let absolute = std::path::absolute(path).ok()?;
    let start = if absolute.is_dir() {
        absolute.as_path()
    } else {
        absolute.parent()?
    };
    start
        .ancestors()
        .find(|dir| dir.join("stilt.toml").is_file())
        .map(Path::to_path_buf)
}

/// Formats one file in place, with what to report on stderr when it can't be.
fn format_file(path: &Path) -> (Outcome, Option<String>) {
    let name = path.display().to_string();
    let refused = |message: String| (Outcome::Refused, Some(message));
    let source = match fs::read(path) {
        Ok(source) => source,
        Err(error) => return refused(format!("{name}: {error}\n")),
    };
    match stilt_fmt::format(&source) {
        Ok(text) if text.as_bytes() == source => (Outcome::Canonical, None),
        Ok(text) => match fs::write(path, text) {
            Ok(()) => (Outcome::Rewritten, None),
            Err(error) => refused(format!("{name}: {error}\n")),
        },
        Err(Error::Syntax(d)) => {
            let text = String::from_utf8_lossy(&source);
            refused(crate::line(&File::new(&name, &text), &d))
        }
        Err(Error::Changed) => refused(format!(
            "{name}: formatting would change what the file means, so it is left as it is\n"
        )),
    }
}

/// The source files at `path`: the file itself, or the `.lt` files under the directory, in
/// order of path.
fn sources(path: &Path) -> io::Result<Vec<PathBuf>> {
    if !fs::metadata(path)?.is_dir() {
        return Ok(vec![path.to_owned()]);
    }
    let mut files = Vec::new();
    walk(path, &mut files)?;
    files.sort();
    Ok(files)
}

fn walk(dir: &Path, files: &mut Vec<PathBuf>) -> io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if entry.file_name().to_string_lossy().starts_with('.') {
            continue;
        }
        if entry.file_type()?.is_dir() {
            walk(&path, files)?;
        } else if path.extension().is_some_and(|e| e == "lt") {
            files.push(path);
        }
    }
    Ok(())
}
