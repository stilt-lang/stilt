//! `stilt new`: a program and a library that check, run and pass their tests as they are
//! written, and the names and places it refuses.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// An empty directory of its own for the test `name`.
fn place(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stilt-new-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("the directory");
    dir
}

fn stilt(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(args)
        .current_dir(dir)
        .output()
        .expect("stilt runs")
}

fn text(out: &[u8]) -> String {
    String::from_utf8_lossy(out).into_owned()
}

#[test]
fn a_new_program_checks_runs_and_passes_its_tests() {
    let dir = place("program");
    let made = stilt(&dir, &["new", "greeter"]);
    assert!(made.status.success(), "{}", text(&made.stderr));
    assert!(
        text(&made.stdout).contains("stilt run"),
        "{}",
        text(&made.stdout)
    );
    let package = dir.join("greeter");
    let manifest = std::fs::read_to_string(package.join("stilt.toml")).expect("a manifest");
    assert_eq!(
        manifest,
        "[package]\nname = \"greeter\"\nedition = \"2027\"\n"
    );
    let checked = stilt(&package, &["check"]);
    assert!(checked.status.success(), "{}", text(&checked.stderr));
    let ran = stilt(&package, &["run"]);
    assert_eq!(text(&ran.stdout), "Hello, greeter!\n");
    let tested = stilt(&package, &["test"]);
    assert!(tested.status.success(), "{}", text(&tested.stdout));
}

#[test]
fn a_new_library_checks_and_passes_its_tests_and_examples() {
    let dir = place("library");
    let made = stilt(&dir, &["new", "--lib", "sums"]);
    assert!(made.status.success(), "{}", text(&made.stderr));
    let package = dir.join("sums");
    let checked = stilt(&package, &["check"]);
    assert!(checked.status.success(), "{}", text(&checked.stderr));
    let tested = stilt(&package, &["test", "--json"]);
    assert!(tested.status.success(), "{}", text(&tested.stdout));
    let report: serde_json::Value = serde_json::from_slice(&tested.stdout).expect("JSON");
    let tests = report["tests"].as_array().expect("tests");
    assert_eq!(tests.len(), 2, "a test and an example: {report}");
}

#[test]
fn a_bad_name_or_a_full_directory_is_refused() {
    let dir = place("refused");
    for name in ["Greeter", "fn", "main", "std", "two-words"] {
        let made = stilt(&dir, &["new", name]);
        assert_eq!(made.status.code(), Some(2), "{name}");
        assert!(!dir.join(name).exists(), "{name}");
    }
    std::fs::create_dir_all(dir.join("taken")).expect("the directory");
    std::fs::write(dir.join("taken/notes.txt"), "mine").expect("a file");
    let made = stilt(&dir, &["new", "taken"]);
    assert_eq!(made.status.code(), Some(2));
    assert!(
        text(&made.stderr).contains("isn't empty"),
        "{}",
        text(&made.stderr)
    );
    assert_eq!(
        std::fs::read_to_string(dir.join("taken/notes.txt")).expect("the file"),
        "mine"
    );
}
