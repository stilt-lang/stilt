//! `stilt test` (program.test-results and program.doc-examples): its verdict, with `done` when
//! there are no errors and every test passes (goal one-verdict) and `repeat` when the program's
//! files are those of an earlier run whose verdict wasn't done (repeated-failures-flagged); the
//! isolation of each test, which a panic or an `exit` ends alone, while a stack overflow ends every
//! test with status 134; and the cached result of a test that doesn't do `io` and whose code hasn't
//! changed. When every test passed, every count is back to zero at the end, the constants the tests
//! computed released, as at the end of a run (goal no-leaks). `test` asks the engine of every
//! program, a single file included, which each test stops.

mod common;

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};

use serde_json::Value;

/// A program of one file in a directory of its own, whose engine is stopped when this is
/// dropped.
struct Program {
    dir: PathBuf,
}

impl Program {
    fn new(name: &str, source: &str) -> Self {
        let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
            .join("verdict")
            .join(name);
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("the directory can be made");
        let program = Self { dir };
        program.write(source);
        program
    }

    fn write(&self, source: &str) {
        fs::write(self.dir.join("main.lt"), source).expect("the program can be written");
    }

    /// `stilt test --json main.lt`, its status, verdict and stderr.
    fn test(&self) -> (i32, Value, String) {
        let output = self.stilt(&["test", "--json", "main.lt"]);
        let verdict = serde_json::from_slice(&output.stdout).unwrap_or(Value::Null);
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        (output.status.code().unwrap_or(-1), verdict, stderr)
    }

    fn stilt(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_stilt"))
            .current_dir(&self.dir)
            .args(args)
            .output()
            .expect("stilt runs")
    }
}

impl Drop for Program {
    fn drop(&mut self) {
        common::stop_engine(&self.dir, "main.lt".as_ref());
    }
}

/// The results of a verdict's tests, by line.
fn results(verdict: &Value) -> Vec<(u64, bool)> {
    verdict["tests"]
        .as_array()
        .map(|tests| {
            tests
                .iter()
                .map(|t| (t["line"].as_u64().unwrap_or(0), t["passed"] == true))
                .collect()
        })
        .unwrap_or_default()
}

const PASSING: &str = "/// Doubles.\n/// ex: double(2) == 4\nfn double(x: i64) -> i64 { x * 2 }\n\ntest \"doubles\" { assert double(3) == 6 }\n";

#[test]
fn a_verdict_is_done_when_every_test_passes() {
    let program = Program::new("done", PASSING);
    let (status, verdict, _) = program.test();
    assert_eq!(status, 0, "{verdict}");
    assert_eq!(verdict["done"], true);
    assert_eq!(verdict["diagnostics"], Value::Array(Vec::new()));
    assert_eq!(results(&verdict), [(2, true), (5, true)]);
    program.write(&PASSING.replace("== 6", "== 7"));
    let (status, verdict, _) = program.test();
    assert_eq!(status, 1);
    assert_eq!(verdict["done"], false);
    assert_eq!(results(&verdict), [(2, true), (5, false)]);
    // A program with errors runs no test (conformance.commands).
    program.write(&PASSING.replace("x * 2", "x * true"));
    let (status, verdict, _) = program.test();
    assert_eq!(status, 1);
    assert_eq!(verdict["done"], false);
    let code = verdict["diagnostics"][0]["code"].as_str().unwrap_or("");
    assert!(code.starts_with('E'), "{verdict}");
    assert_eq!(results(&verdict), []);
}

#[test]
fn a_verdict_marks_files_that_failed_before() {
    let failing = PASSING.replace("== 6", "== 7");
    let program = Program::new("repeat", &failing);
    let (_, first, _) = program.test();
    assert_eq!(
        (&first["done"], &first["repeat"]),
        (&false.into(), &false.into())
    );
    let (_, second, _) = program.test();
    assert_eq!(second["repeat"], true, "the same files failed before");
    program.write(&failing.replace("== 7", "== 8"));
    let (_, edited, _) = program.test();
    assert_eq!(edited["repeat"], false, "other files");
    program.write(PASSING);
    let (_, passing, _) = program.test();
    let (_, again, _) = program.test();
    assert_eq!(
        (&passing["done"], &passing["repeat"]),
        (&true.into(), &false.into())
    );
    assert_eq!(again["repeat"], false, "these files passed before");
    program.write(&failing);
    let (_, back, _) = program.test();
    assert_eq!(back["repeat"], true, "the first files again");
}

#[test]
fn a_panic_or_an_exit_ends_only_its_test() {
    let source = "test \"panics\" {\n  let xs = [1]\n  assert xs[1] == 1\n}\n\ntest \"exits\" { exit(0) }\n\ntest \"raises\" { raise \"no\" }\n\ntest \"runs\" { assert true }\n";
    let program = Program::new("isolation", source);
    let (status, verdict, stderr) = program.test();
    assert_eq!(status, 1);
    assert_eq!(
        results(&verdict),
        [(1, false), (6, false), (8, false), (10, true)]
    );
    assert!(stderr.contains("panic: bounds: "), "{stderr}");
}

#[test]
fn a_stack_overflow_ends_every_test() {
    let source = "fn down(n: i64) -> i64 { if n == 0 { 0 } else { 1 + down(n - 1) } }\n\ntest \"first\" { assert down(10) == 10 }\n\ntest \"overflows\" { assert down(1000000000) == 0 }\n\ntest \"last\" { assert true }\n";
    let program = Program::new("overflow", source);
    let output = program.stilt(&["test", "--json", "main.lt"]);
    assert_eq!(output.status.code(), Some(134));
    assert!(output.stdout.is_empty(), "no test reports a result");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.ends_with("fatal: stack overflow\n"), "{stderr}");
}

#[test]
fn tests_print_to_stderr_and_the_failures_and_the_count_go_to_stdout() {
    let source =
        "test \"prints\" { print(\"hello\") }\n\n/// One.\n/// ex: 1 == 2\nfn one() -> i64 { 1 }\n";
    let program = Program::new("lines", source);
    let output = program.stilt(&["test", "main.lt"]);
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        stdout,
        "main.lt:4: example `1 == 2` failed\n  left:  1\n  right: 2\n1 passed, 1 failed\n"
    );
    assert!(String::from_utf8_lossy(&output.stderr).contains("hello\n"));
}

#[test]
fn a_failure_shows_why_it_failed() {
    let source = "/// ex: 1 + 1 == 3\n/// prop: |n: i64, s: str| n < 0\nfn f() {}\n\ntest \"lists\" { assert [1, 2] == [1, 3] }\n\ntest \"raises\" { raise \"no\" }\n\ntest \"exits\" { exit(3) }\n";
    let program = Program::new("why", source);
    let output = program.stilt(&["test", "main.lt"]);
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8_lossy(&output.stdout);
    for expected in [
        "main.lt:1: example `1 + 1 == 3` failed\n  left:  2\n  right: 3\n",
        "main.lt:2: property `|n: i64, s: str| n < 0` failed\n",
        "    n = 0\n    s = \"\"\n",
        "main.lt:5: test \"lists\" failed\n  panic: assert: the assertion is false: [1, 2] == [1, 3]\n    at main.lt:5:",
        "main.lt:7: test \"raises\" failed\n  raised no\n",
        "main.lt:9: test \"exits\" failed\n  called `exit`\n",
        "0 passed, 5 failed\n",
    ] {
        assert!(
            stdout.contains(expected),
            "{expected:?} is missing from\n{stdout}"
        );
    }
}

#[test]
fn a_test_without_io_reuses_its_result_until_its_code_changes() {
    let source = "fn limit() -> i64 { 3 }\n\ntest \"pure\" { assert limit() == 4 }\n\ntest \"io\" {\n  print(\"ran\")\n  assert limit() == 3\n}\n";
    let program = Program::new("cached", source);
    let (_, first, stderr) = program.test();
    assert_eq!(results(&first), [(3, false), (5, true)]);
    assert!(
        stderr.contains("panic: assert: "),
        "the pure test ran: {stderr}"
    );
    assert!(stderr.contains("ran\n"), "the test with io ran: {stderr}");
    let (_, second, stderr) = program.test();
    assert_eq!(results(&second), [(3, false), (5, true)]);
    assert!(
        !stderr.contains("panic: "),
        "the pure test's result is reused: {stderr}"
    );
    assert!(
        stderr.contains("ran\n"),
        "a test with io always runs: {stderr}"
    );
    // An edit of a function that the test reaches runs it again.
    program.write(&source.replace("{ 3 }", "{ 4 }").replace("== 3", "== 4"));
    let (_, third, _) = program.test();
    assert_eq!(results(&third), [(3, true), (5, true)]);
    program.write(&source.replace("{ 3 }", "{ 2 }"));
    let (_, fourth, stderr) = program.test();
    assert_eq!(results(&fourth), [(3, false), (5, false)]);
    assert!(
        stderr.contains("panic: assert: "),
        "the edit ran it again: {stderr}"
    );
}

#[test]
fn passing_tests_end_with_every_count_at_zero() {
    let source = "const NAMES: List<str> = [\"ana\", \"bo\"]\n\ntype Tree = | Leaf | Node(Tree, i64, Tree)\n\nfn size(t: Tree) -> i64 {\n  match t {\n    Leaf => 0\n    Node(l, _, r) => size(l) + 1 + size(r)\n  }\n}\n\n/// Joins the names.\n/// ex: joined() == \"ana,bo\"\nfn joined() -> str { \",\".join(NAMES) }\n\ntest \"trees\" { assert size(Node(Node(Leaf, 1, Leaf), 2, Leaf)) == 2 }\n\ntest \"maps and closures\" {\n  var m: Map<str, List<i64>> = Map.new()\n  for name in NAMES { m[name] = [name.len()] }\n  let lens = NAMES.map(|n| m[n][0])\n  assert lens == [3, 2]\n}\n";
    let program = Program::new("counts", source);
    let (status, verdict, stderr) = program.test();
    assert_eq!(status, 0, "{verdict} {stderr}");
    assert_eq!(verdict["done"], true);
    assert_eq!(results(&verdict), [(13, true), (16, true), (18, true)]);
    assert!(!stderr.contains("never freed"), "{stderr}");
}

#[test]
fn each_result_names_its_kind_and_a_failure_says_why() {
    // conformance.test-objects: the compiler's objects add fields, each result its kind and name,
    // and a failure the lines that `test` without `--json` writes for it (program.test-results).
    let program = Program::new(
        "kinds",
        "/// ex: twice(1) == 3\nfn twice(n: i64) -> i64 { n * 2 }\n\ntest \"doubles\" { assert twice(2) == 4 }\n",
    );
    let (status, verdict, _) = program.test();
    assert_eq!(status, 1, "{verdict}");
    let example = &verdict["tests"][0];
    assert_eq!(example["kind"], "example", "{verdict}");
    assert_eq!(example["name"], "twice(1) == 3");
    // A comparison that fails shows its two sides, as the report without `--json` does.
    assert_eq!(example["why"], serde_json::json!(["left:  2", "right: 3"]));
    let test = &verdict["tests"][1];
    assert_eq!(test["kind"], "test");
    assert_eq!(test["name"], "doubles");
    assert_eq!(test["why"], Value::Null);
}
