//! `stilt fmt` (syntax.format and syntax.no-options; Inferred facts, "Seven commands"): it
//! rewrites in place the files that aren't canonical, lists them, and exits with status 1 unless
//! every file was already canonical; it leaves a file with a syntax error as it is, and reports its
//! error. The format itself is tested by the formatter's tests in `tests/format/`.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// Runs `stilt fmt` with `args` in `dir`.
fn fmt(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stilt"))
        .arg("fmt")
        .args(args)
        .current_dir(dir)
        .output()
        .expect("stilt runs")
}

/// An empty directory for one test.
fn directory(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("fmt")
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    dir
}

const MESSY: &str = "fn main() {\n    let x = 1; print(\"{x}\")\n}\n";
const CANONICAL: &str = "fn main() {\n  let x = 1\n  print(\"{x}\")\n}\n";

#[test]
fn files_that_are_not_canonical_are_rewritten_and_listed() {
    let dir = directory("rewritten");
    fs::create_dir_all(dir.join("lib")).expect("a module directory");
    fs::create_dir_all(dir.join(".hidden")).expect("a hidden directory");
    fs::write(dir.join("main.lt"), MESSY).expect("a file");
    fs::write(dir.join("lib/util.lt"), CANONICAL).expect("a file");
    fs::write(dir.join(".hidden/skipped.lt"), MESSY).expect("a file");
    fs::write(dir.join("notes.txt"), MESSY).expect("a file");
    let output = fmt(&dir, &[]);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(String::from_utf8_lossy(&output.stdout), "./main.lt\n");
    assert_eq!(fs::read_to_string(dir.join("main.lt")).unwrap(), CANONICAL);
    assert_eq!(
        fs::read_to_string(dir.join(".hidden/skipped.lt")).unwrap(),
        MESSY
    );
    assert_eq!(fs::read_to_string(dir.join("notes.txt")).unwrap(), MESSY);
    let again = fmt(&dir, &["."]);
    assert!(again.status.success(), "every file is canonical now");
    assert_eq!(String::from_utf8_lossy(&again.stdout), "");
}

#[test]
fn a_file_is_formatted_by_its_path() {
    let dir = directory("one_file");
    fs::write(dir.join("a.lt"), MESSY).expect("a file");
    fs::write(dir.join("b.lt"), MESSY).expect("a file");
    let output = fmt(&dir, &["a.lt"]);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(String::from_utf8_lossy(&output.stdout), "a.lt\n");
    assert_eq!(fs::read_to_string(dir.join("a.lt")).unwrap(), CANONICAL);
    assert_eq!(fs::read_to_string(dir.join("b.lt")).unwrap(), MESSY);
}

#[test]
fn a_file_with_a_syntax_error_is_left_as_it_is_and_reported() {
    let dir = directory("syntax_error");
    let broken = "fn main() {\n    let = 1\n}\n";
    fs::write(dir.join("broken.lt"), broken).expect("a file");
    fs::write(dir.join("fine.lt"), CANONICAL).expect("a file");
    let output = fmt(&dir, &[]);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(String::from_utf8_lossy(&output.stdout), "");
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "./broken.lt:2:9: E0100: expected a pattern, found `=`\n"
    );
    assert_eq!(fs::read_to_string(dir.join("broken.lt")).unwrap(), broken);
}

#[test]
fn a_path_that_does_not_exist_is_refused() {
    let dir = directory("missing");
    let output = fmt(&dir, &["nowhere"]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).starts_with("nowhere: "));
}
