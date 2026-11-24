//! `stilt diff`: the API changes between two versions of a package, and the version they need
//! (versions.api and versions.change-needed).

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// A package `name` in `dir`, whose module `main` is `main`.
fn package(dir: &Path, name: &str, main: &str) -> PathBuf {
    let path = dir.join(name);
    std::fs::create_dir_all(path.join("src")).expect("the directory");
    std::fs::write(path.join("stilt.toml"), "[package]\nname = \"sums\"\n").expect("a manifest");
    std::fs::write(path.join("src/main.lt"), main).expect("a module");
    path
}

fn diff(args: &[&Path], from: Option<&str>) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_stilt"));
    command.arg("diff").args(args);
    if let Some(v) = from {
        command.args(["--from", v]);
    }
    command.output().expect("stilt runs")
}

fn place(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stilt-diff-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

const TOTAL: &str = "pub fn total(n: i64) -> i64 {\n  n\n}\n";

#[test]
fn an_added_function_needs_a_minor_version_and_a_gained_fact_a_major_one() {
    let dir = place("changes");
    let old = package(&dir, "old", TOTAL);
    let added = package(
        &dir,
        "added",
        &format!("{TOTAL}\npub fn zero() -> i64 {{\n  0\n}}\n"),
    );
    let out = diff(&[&old, &added], Some("1.4.2"));
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let expected = "minor  adds `sums.zero`\nneeds a new minor version: 1.4.2 → 1.5.0\n";
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
    let looping = "pub fn total(n: i64) -> i64 {\n  var i = 0\n  while i < n { i += 1 }\n  i\n}\n";
    let gained = package(&dir, "gained", looping);
    let out = diff(&[&old, &gained], None);
    // `i += 1` can overflow (effects.overflow-effect), and the `while` may not end (facts.div).
    let expected = "major  gains `overflow` in `sums.total`\n\
                    major  gains `div` in `sums.total`\nneeds a new major version\n";
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
    let out = diff(&[&old, &old], Some("1.4.2"));
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "needs only a new patch version: 1.4.2 → 1.4.3\n"
    );
}

#[test]
fn a_side_with_an_error_or_a_bad_version_is_refused() {
    let dir = place("refused");
    let old = package(&dir, "old", TOTAL);
    let broken = package(&dir, "broken", "pub fn total(n: i64) -> i64 { \"n\" }\n");
    let out = diff(&[&old, &broken], None);
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).contains("E0311"));
    let out = diff(&[&old, &old], Some("one"));
    assert_eq!(out.status.code(), Some(2));
}
