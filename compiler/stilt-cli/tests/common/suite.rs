//! The test suites of `tests/` that `stilt show --json` is checked against: the facts suite and
//! the holes suite. A program is a `.lt` file, or a directory that holds one, as in the
//! conformance suite.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

/// The suite under `tests/`, by its directory's name.
pub(crate) fn root(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests")
        .join(name)
}

/// The programs of a suite: each `.lt` file, and each directory, which holds a program.
pub(crate) fn programs(root: &Path) -> Vec<PathBuf> {
    let mut all: Vec<PathBuf> = fs::read_dir(root)
        .expect("the suite is readable")
        .map(|e| e.expect("the suite is readable").path())
        .filter(|p| {
            let name = p.file_name().unwrap_or_default().to_string_lossy();
            !name.starts_with(['_', '.'])
                && (p.is_dir() || p.extension().is_some_and(|e| e == "lt"))
        })
        .collect();
    all.sort();
    all
}

/// The modules of a program: each one's name, and its file, by the path that reports give it
/// (program.report-paths and program.module-names).
pub(crate) fn modules(program: &Path) -> Vec<(String, String)> {
    if !program.is_dir() {
        let name = program.file_name().unwrap_or_default().to_string_lossy();
        return vec![("main".to_owned(), name.into_owned())];
    }
    let mut found: Vec<(String, String)> = fs::read_dir(program)
        .expect("the program is readable")
        .map(|e| e.expect("the program is readable").path())
        .filter(|p| p.extension().is_some_and(|e| e == "lt"))
        .map(|p| {
            let file = p
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .into_owned();
            (file.trim_end_matches(".lt").to_owned(), file)
        })
        .collect();
    found.sort();
    found
}

/// The source file of a program, by the path that reports give it.
pub(crate) fn source(program: &Path, file: &str) -> PathBuf {
    if program.is_dir() {
        program.join(file)
    } else {
        program.to_path_buf()
    }
}

/// The record that `stilt show --json` gives a module of the program, which must succeed with
/// nothing on stderr.
pub(crate) fn show_module(program: &Path, module: &str) -> Result<Value, String> {
    let (dir, path) = if program.is_dir() {
        (program.to_path_buf(), PathBuf::from("."))
    } else {
        let dir = program
            .parent()
            .expect("a file has a directory")
            .to_path_buf();
        (
            dir,
            PathBuf::from(program.file_name().expect("a file has a name")),
        )
    };
    let output = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["show", "--json", module])
        .arg(&path)
        .current_dir(&dir)
        .output()
        .expect("stilt runs");
    super::stop_engine(&dir, &path);
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !output.status.success() || !stderr.is_empty() {
        return Err(format!("`show --json {module}` failed: {stderr}"));
    }
    serde_json::from_slice(&output.stdout).map_err(|e| e.to_string())
}
