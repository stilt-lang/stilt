//! `stilt run` on programs with errors (program.programs-with-errors and
//! program.errors-in-bodies): the diagnostics come first, every function or constant whose body has
//! an error panics with `check-error` where it is reached, at its name, and the program exits with
//! status 2 however it ends.

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};

/// Runs `source`, written to a file of its own, with `stilt run`.
fn run(name: &str, source: &str) -> Output {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("errors");
    fs::create_dir_all(&dir).expect("the directory can be made");
    fs::write(dir.join(format!("{name}.lt")), source).expect("the program can be written");
    Command::new(env!("CARGO_BIN_EXE_stilt"))
        .current_dir(&dir)
        .args(["run", &format!("{name}.lt")])
        .output()
        .expect("stilt runs")
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// The panic report, the last two lines of stderr (program.panic-report), or nothing.
fn report(output: &Output) -> (String, String) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    let lines: Vec<&str> = stderr.lines().collect();
    match lines.as_slice() {
        [.., kind, at] if kind.starts_with("panic: ") => ((*kind).to_owned(), (*at).to_owned()),
        _ => (String::new(), String::new()),
    }
}

/// Checks that the program ended with status 2, having printed `printed`, with a `check-error`
/// panic at `at`.
fn panics_at(output: &Output, printed: &str, at: &str) {
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert_eq!(stdout(output), printed, "{output:?}");
    let (kind, location) = report(output);
    assert!(kind.starts_with("panic: check-error: "), "{output:?}");
    assert_eq!(location, format!("  at {at}"), "{output:?}");
}

#[test]
fn an_error_never_reached_leaves_the_output_with_status_2() {
    let source = "fn unused() -> i64 { missing }\n\nfn main() / io {\n  print(\"done\")\n}\n";
    let output = run("unreached", source);
    assert_eq!(output.status.code(), Some(2));
    assert_eq!(stdout(&output), "done\n");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("E0211"),
        "the diagnostics come first: {stderr}"
    );
}

#[test]
fn a_function_with_an_error_panics_at_its_name_when_called() {
    let source = "fn broken(x: i64) -> i64 {\n  x + missing\n}\n\nfn twice(x: i64) -> i64 { x * 2 }\n\nfn main() / io {\n  print(\"{twice(21)}\")\n  print(\"{broken(1)}\")\n  print(\"never\")\n}\n";
    panics_at(&run("body", source), "42\n", "body.lt:1:4");
}

#[test]
fn an_error_in_a_signature_breaks_its_callers() {
    let source = "fn broken(x: Unknown) -> i64 { 1 }\n\nfn caller() -> i64 { broken(1) }\n\nfn main() / io {\n  print(\"before\")\n  print(\"{caller()}\")\n}\n";
    panics_at(&run("signature", source), "before\n", "signature.lt:3:4");
}

#[test]
fn a_constant_with_an_error_panics_where_it_is_read() {
    let source = "const LIMIT: i64 = \"ten\"\n\nfn main() / io {\n  print(\"start\")\n  print(\"{LIMIT}\")\n}\n";
    panics_at(&run("constant", source), "start\n", "constant.lt:1:7");
}

#[test]
fn a_type_with_an_error_breaks_only_what_builds_or_reads_the_field() {
    let source = "type Point = { x: i64, y: Nope }\n\nfn first(p: Point) -> i64 { p.x }\n\nfn count(ps: List<Point>) -> i64 { ps.len() }\n\nfn make() -> Point { Point { x: 1, y: 2 } }\n\nfn main() / io {\n  print(\"{count([])}\")\n  print(\"{first(make())}\")\n}\n";
    panics_at(&run("type", source), "0\n", "type.lt:7:4");
}

#[test]
fn an_error_in_main_panics_as_the_program_starts() {
    let source = "fn main() / io {\n  print(\"never\")\n  let n: i64 = \"one\"\n}\n";
    panics_at(&run("main", source), "", "main.lt:1:4");
}

#[test]
fn a_method_that_an_impl_lacks_panics_at_the_impl() {
    let source = "trait Describe {\n  fn describe(self) -> str\n  fn tag(self) -> str\n}\n\ntype T = { a: i64 }\n\nimpl Describe for T {\n  fn tag(self) -> str { \"t\" }\n}\n\nfn main() / io {\n  print(T { a: 1 }.tag())\n  print(T { a: 1 }.describe())\n}\n";
    panics_at(&run("impl", source), "t\n", "impl.lt:8:1");
}

#[test]
fn a_syntax_error_in_a_function_leaves_the_rest_running() {
    let source = "fn half(x: i64) -> i64 { x / }\n\nfn twice(x: i64) -> i64 { x * 2 }\n\nfn main() / io {\n  print(\"{twice(4)}\")\n  print(\"{half(4)}\")\n}\n";
    panics_at(&run("syntax", source), "8\n", "syntax.lt:1:4");
}

#[test]
fn a_function_whose_signature_a_syntax_error_hides_breaks_its_callers() {
    let source = "fn half(x: i64) -> { x }\n\nfn twice(x: i64) -> i64 { half(x) * 2 }\n\nfn main() / io {\n  print(\"start\")\n  print(\"{twice(4)}\")\n}\n";
    panics_at(&run("hidden", source), "start\n", "hidden.lt:3:4");
}

#[test]
fn a_type_with_a_syntax_error_has_no_values() {
    // Every use of a type whose part breaks has the error type (errors.error-type and
    // errors.broken-parts), so `count` and `make` have signatures that hold it, and `main`, which
    // calls them, panics as soon as the program starts (program.meeting-the-error-type).
    let source = "type Point = { x: i64, y: }\n\nfn count(ps: List<Point>) -> i64 { ps.len() }\n\nfn make() -> Point { Point { x: 1 } }\n\nfn main() / io {\n  print(\"{count([])}\")\n  let p = make()\n}\n";
    panics_at(&run("syntax_type", source), "", "syntax_type.lt:7:4");
}

#[test]
fn a_program_with_errors_exits_with_status_2_however_it_ends() {
    let unused = "fn unused() -> i64 { missing }\n\n";
    let ends = [
        ("exits", "fn main() / io {\n  exit(7)\n}\n"),
        ("raises", "fn main() / raise<str> {\n  raise \"boom\"\n}\n"),
        ("panics", "fn main() {\n  panic(\"stop\")\n}\n"),
    ];
    for (name, main) in ends {
        let output = run(name, &format!("{unused}{main}"));
        assert_eq!(output.status.code(), Some(2), "{name}: {output:?}");
    }
}

#[test]
fn a_program_without_main_still_doesnt_run() {
    let output = run("no_main", "fn helper() -> i64 { missing }\n");
    assert_eq!(output.status.code(), Some(2));
    assert_eq!(stdout(&output), "");
}
