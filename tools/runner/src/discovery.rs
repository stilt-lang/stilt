//! Finding tests on disk (conformance.location and conformance.directory-tests).
//!
//! A `.lt` file is a single-file test, and a directory that holds `main.lt` is a directory
//! test, whose annotations the runner reads in its `.lt` files and in its manifests, the
//! `stilt.toml` files of its packages (packages.manifest). While walking a
//! directory, entries whose names start with `_` or `.` are skipped, so drafts in `_pending/` don't
//! run until they are approved.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::annotations::SourceFile;

/// A test found on disk, with its files loaded.
#[derive(Debug)]
pub(crate) struct Test {
    /// The test's path as it is reported, with `/` as the separator.
    pub(crate) name: String,
    /// The working directory of every command the test runs.
    pub(crate) dir: PathBuf,
    /// The `PATH` argument of the protocol, relative to `dir`.
    pub(crate) target: String,
    /// The file that holds the header annotations.
    pub(crate) header_file: String,
    pub(crate) files: Vec<SourceFile>,
}

/// Finds every test under `roots`, sorted by name.
pub(crate) fn discover(roots: &[PathBuf]) -> io::Result<Vec<Test>> {
    let mut tests = Vec::new();
    for root in roots {
        let metadata = fs::metadata(root).map_err(|error| with_path(root, &error))?;
        if metadata.is_dir() {
            visit(root, &mut tests)?;
        } else {
            tests.push(single_file(root)?);
        }
    }
    tests.sort_by(|a, b| a.name.cmp(&b.name));
    tests.dedup_by(|a, b| a.name == b.name);
    Ok(tests)
}

fn visit(dir: &Path, tests: &mut Vec<Test>) -> io::Result<()> {
    if dir.join("main.lt").is_file() {
        tests.push(directory_test(dir)?);
        return Ok(());
    }
    for path in entries(dir)? {
        if path.is_dir() {
            visit(&path, tests)?;
        } else if is_source(&path) {
            tests.push(single_file(&path)?);
        }
    }
    Ok(())
}

fn single_file(path: &Path) -> io::Result<Test> {
    let dir = match path.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent.to_owned(),
        _ => PathBuf::from("."),
    };
    let target = path
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_default();
    let text = read(path)?;
    Ok(Test {
        name: display(path),
        dir,
        header_file: target.clone(),
        files: vec![SourceFile {
            path: target.clone(),
            text,
        }],
        target,
    })
}

fn directory_test(dir: &Path) -> io::Result<Test> {
    let mut files = Vec::new();
    collect_sources(dir, "", &mut files)?;
    Ok(Test {
        name: display(dir),
        dir: dir.to_owned(),
        target: ".".to_owned(),
        header_file: "main.lt".to_owned(),
        files,
    })
}

/// Loads every `.lt` file and manifest under `dir`, naming each by its path from the test's
/// directory.
fn collect_sources(dir: &Path, prefix: &str, files: &mut Vec<SourceFile>) -> io::Result<()> {
    for path in entries(dir)? {
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        let relative = format!("{prefix}{name}");
        if path.is_dir() {
            collect_sources(&path, &format!("{relative}/"), files)?;
        } else if is_source(&path) || is_manifest(&path) {
            files.push(SourceFile {
                path: relative,
                text: read(&path)?,
            });
        }
    }
    Ok(())
}

/// The entries of `dir` in name order, without those whose names start with `_` or `.`.
pub(crate) fn entries(dir: &Path) -> io::Result<Vec<PathBuf>> {
    let mut paths = Vec::new();
    for entry in fs::read_dir(dir).map_err(|error| with_path(dir, &error))? {
        let entry = entry?;
        if !entry.file_name().to_string_lossy().starts_with(['_', '.']) {
            paths.push(entry.path());
        }
    }
    paths.sort();
    Ok(paths)
}

fn is_source(path: &Path) -> bool {
    path.is_file() && path.extension().is_some_and(|extension| extension == "lt")
}

/// Whether `path` is a package's manifest, whose TOML comments may hold inline annotations.
fn is_manifest(path: &Path) -> bool {
    path.is_file() && path.file_name().is_some_and(|name| name == "stilt.toml")
}

/// Reads a source file. Invalid UTF-8 is kept as replacement characters, since some tests
/// check that implementations reject it.
fn read(path: &Path) -> io::Result<String> {
    let bytes = fs::read(path).map_err(|error| with_path(path, &error))?;
    Ok(String::from_utf8_lossy(&bytes).into_owned())
}

/// A path as tests are named, with `/` as the separator.
pub(crate) fn display(path: &Path) -> String {
    path.to_string_lossy().replace('\\', "/")
}

/// Empties `dir`, creating it if it doesn't exist.
pub(crate) fn empty_dir(dir: &Path) -> io::Result<()> {
    match fs::remove_dir_all(dir) {
        Err(error) if error.kind() != io::ErrorKind::NotFound => return Err(error),
        _ => {}
    }
    fs::create_dir_all(dir)
}

fn with_path(path: &Path, error: &io::Error) -> io::Error {
    io::Error::new(error.kind(), format!("{}: {error}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A temporary directory, removed when dropped.
    struct Scratch(PathBuf);

    impl Scratch {
        fn new(name: &str) -> Self {
            let dir =
                std::env::temp_dir().join(format!("stilt-test-{name}-{}", std::process::id()));
            let _ = fs::remove_dir_all(&dir);
            fs::create_dir_all(&dir).unwrap();
            Self(dir)
        }

        fn file(&self, path: &str, text: &str) {
            let path = self.0.join(path);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, text).unwrap();
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn finds_single_file_and_directory_tests_in_order() {
        let scratch = Scratch::new("discover");
        scratch.file("lex/b.lt", "");
        scratch.file("lex/a.lt", "");
        scratch.file("lex/notes.md", "");
        scratch.file("modules/cycle/main.lt", "");
        scratch.file("modules/cycle/a/b.lt", "");
        scratch.file("modules/cycle/stilt.toml", "");
        scratch.file("modules/cycle/notes.toml", "");
        scratch.file("_pending/draft.lt", "");
        scratch.file(".hidden/x.lt", "");

        let tests = discover(std::slice::from_ref(&scratch.0)).unwrap();
        let root = display(&scratch.0);
        let names: Vec<_> = tests
            .iter()
            .map(|test| test.name.strip_prefix(&root).unwrap())
            .collect();
        assert_eq!(names, ["/lex/a.lt", "/lex/b.lt", "/modules/cycle"]);

        let single = &tests[0];
        assert_eq!(single.target, "a.lt");
        assert_eq!(single.header_file, "a.lt");
        assert_eq!(single.dir, scratch.0.join("lex"));

        let directory = &tests[2];
        assert_eq!(directory.target, ".");
        let files: Vec<_> = directory
            .files
            .iter()
            .map(|file| file.path.as_str())
            .collect();
        assert_eq!(files, ["a/b.lt", "main.lt", "stilt.toml"]);
    }

    #[test]
    fn an_explicit_root_is_used_even_when_its_name_starts_with_an_underscore() {
        let scratch = Scratch::new("explicit");
        scratch.file("_pending/draft.lt", "");
        let tests = discover(&[scratch.0.join("_pending")]).unwrap();
        assert_eq!(tests.len(), 1);
    }

    #[test]
    fn a_missing_root_is_an_error_that_names_it() {
        let error = discover(&[PathBuf::from("/no/such/dir")]).unwrap_err();
        assert!(error.to_string().starts_with("/no/such/dir: "));
    }
}
