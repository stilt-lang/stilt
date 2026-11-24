//! Tests reading the annotations of whole files: what each kind of test expects, and why a
//! malformed one is rejected.

use super::*;

fn spec(text: &str) -> Result<Spec, Malformed> {
    let file = SourceFile {
        path: "main.lt".to_owned(),
        text: text.to_owned(),
    };
    parse(&[file], "main.lt")
}

fn reason(text: &str) -> String {
    spec(text).unwrap_err().reason
}

fn run(text: &str) -> RunSpec {
    match spec(text).unwrap().kind {
        Kind::Run(run) => run,
        kind => panic!("expected a run test, found {kind:?}"),
    }
}

#[test]
fn a_file_without_annotations_is_a_core_run_test_with_empty_output() {
    let spec = spec("fn main() {}\n").unwrap();
    assert_eq!(spec.tier, Tier::Core);
    assert_eq!(spec.diagnostics, Vec::<Diagnostic>::new());
    assert!(matches!(spec.kind, Kind::Run(run) if run == RunSpec::default()));
}

#[test]
fn reads_every_header_key() {
    let spec = spec(concat!(
        "//~ tier: advanced\n",
        "//~ rule: numbers.integer-panics, lexical.commented-out-code.single-token\n",
        "//~ args: a \"b c\" \"\\\"\"\n",
        "//~ stdin: \"x\\ty\\r\\n\\xff\"\n",
        "//~ stdout:\n",
        "//~ | first\n",
        "//~ |\n",
        "//~ stderr:\n",
        "//~ |   indented\n",
        "//~ panic: bounds\n",
        "//~ panic-at: a/b.lt:4:12\n",
        "fn main() {}\n",
    ))
    .unwrap();
    assert_eq!(spec.tier, Tier::Advanced);
    assert_eq!(
        spec.rules,
        [
            "numbers.integer-panics",
            "lexical.commented-out-code.single-token"
        ]
    );
    let Kind::Run(run) = spec.kind else {
        panic!("expected a run test")
    };
    assert_eq!(run.args, ["a", "b c", "\""]);
    assert_eq!(run.stdin, b"x\ty\r\n\xff");
    assert_eq!(run.panic_at.as_deref(), Some("a/b.lt:4:12"));
    assert_eq!(run.stdout, "first\n\n");
    assert_eq!(run.stderr.as_deref(), Some("  indented\n"));
    assert_eq!(run.exit, 101);
    assert_eq!(run.panic.as_deref(), Some("bounds"));
}

#[test]
fn run_output_adds_one_newline() {
    assert_eq!(run("//~ run-output: \"hi\"\n").stdout, "hi\n");
}

#[test]
fn exit_defaults_to_zero() {
    assert_eq!(run("//~ exit: 3\n").exit, 3);
    assert_eq!(run("").exit, 0);
}

#[test]
fn inline_entries_make_check_and_test_block_tests() {
    let check = spec("fn f() {} //~ ERROR E0404 WARN W0002\n").unwrap();
    assert!(matches!(check.kind, Kind::Check));
    let codes: Vec<_> = check.diagnostics.iter().map(ToString::to_string).collect();
    assert_eq!(codes, ["E0404 at main.lt:1", "W0002 at main.lt:1"]);

    let tests =
        spec("/// ex: true //~ PASS\nfn f() {}\ntest \"t\" { assert false } //~ FAIL\n").unwrap();
    let Kind::TestBlocks(results) = tests.kind else {
        panic!("expected a test-block test")
    };
    assert_eq!(results.len(), 2);
    assert!(results[0].passed && results[0].line == 1);
    assert!(!results[1].passed && results[1].line == 3);
}

#[test]
fn a_run_test_with_errors_exits_with_status_2() {
    let spec = spec("//~ run-output: \"a\"\nf() //~ ERROR E0211\n").unwrap();
    assert_eq!(spec.diagnostics.len(), 1);
    let Kind::Run(run) = spec.kind else {
        panic!("expected a run test")
    };
    assert_eq!((run.exit, run.stdout.as_str()), (2, "a\n"));
    let panics = self::run("//~ panic: check-error\nf() //~ ERROR E0211\n");
    assert_eq!(panics.exit, 2);
    assert_eq!(panics.panic.as_deref(), Some("check-error"));
    assert_eq!(self::run("//~ exit: 2\nf() //~ ERROR E0211\n").exit, 2);
}

#[test]
fn a_run_test_may_expect_warnings() {
    let spec = spec("//~ run-output: \"1\"\nfn f() -> i64 = ? //~ WARN W0010\n").unwrap();
    assert_eq!(spec.diagnostics.len(), 1);
    assert!(matches!(spec.kind, Kind::Run(_)));
}

#[test]
fn rejects_malformed_header_annotations() {
    assert_eq!(reason("//~ colour: red\n"), "unknown key `colour`");
    assert_eq!(
        reason("//~ exit: 1\n//~ exit: 2\n"),
        "`exit` is given twice"
    );
    assert_eq!(
        reason("//~ panic-at: main.lt:4:7\nfn main() {}\n"),
        "`panic-at` needs `panic`"
    );
    assert_eq!(
        reason("//~ exit: 2\n//~ stderr:\n//~ | x\nfn main() {}\n"),
        "a test that expects status 2 can't have a `stderr` block"
    );
    assert_eq!(
        reason("//~ stdout: x\n"),
        "`stdout:` takes no value; its lines follow as `//~ |`"
    );
    assert_eq!(reason("//~ | x\n"), "a `//~ |` line outside a block");
    assert_eq!(reason("//~tier: core\n"), "expected a space after `//~`");
    assert_eq!(
        reason("//~ tier core\n"),
        "expected `key: value`, found `tier core`"
    );
}

#[test]
fn rejects_malformed_header_values() {
    assert_eq!(
        reason("//~ exit: 256\n"),
        "`256` is not an exit status from 0 to 255"
    );
    assert_eq!(reason("//~ tier: expert\n"), "unknown tier `expert`");
    for id in [
        "Lexical.case",
        "lexical..case",
        "lexical",
        "lexical.case-",
        "std_io.read",
        "a.b.c.d",
    ] {
        assert_eq!(
            reason(&format!("//~ rule: {id}\n")),
            format!("`{id}` is not a paragraph ID such as `values.independent-copies`")
        );
    }
    assert_eq!(
        reason("//~ panic: compile-error\n"),
        "unknown panic kind `compile-error`"
    );
    assert_eq!(
        reason("//~ stdin: x\n"),
        "expected a quoted string, found `x`"
    );
    assert_eq!(reason("//~ stdin: \"a\\q\"\n"), "unknown escape `\\q`");
    assert_eq!(
        reason("//~ stdin: \"\\x4\"\n"),
        "`\\x4\"` needs two hexadecimal digits"
    );
    assert_eq!(
        reason("//~ run-output: \"\\xff\"\n"),
        "only `stdin` may hold bytes that aren't UTF-8"
    );
    assert_eq!(
        reason("//~ panic-at: main.lt:4\n"),
        "`main.lt:4` is not a location such as `main.lt:4:7`"
    );
    assert_eq!(reason("//~ stdin: \"a\n"), "unterminated quoted string");
    assert_eq!(
        reason("//~ stdin: \"a\" b\n"),
        "unexpected text after the closing quote: ` b`"
    );
    assert_eq!(reason("//~ args: a\"b\n"), "`a\"b` must be quoted");
    assert_eq!(
        reason("//~ args: \"a\"b\n"),
        "a quoted word must be followed by a space"
    );
}

#[test]
fn rejects_malformed_inline_annotations() {
    assert_eq!(reason("f() //~\n"), "empty annotation");
    assert_eq!(reason("f() //~ ERROR\n"), "`ERROR` needs a code");
    assert_eq!(
        reason("f() //~ ERROR W0001\n"),
        "`W0001` is not a code of the form E0000"
    );
    assert_eq!(
        reason("f() //~ WARN W01\n"),
        "`W01` is not a code of the form W0000"
    );
    assert_eq!(reason("f() //~ NOTE x\n"), "unknown entry `NOTE`");
    assert_eq!(
        reason("f() //~ PASS FAIL\n"),
        "more than one `PASS` or `FAIL` on one line"
    );
}

#[test]
fn rejects_combinations_that_rule_10_forbids() {
    assert_eq!(
        reason("//~ run-output: \"a\"\n//~ stdout:\n//~ | a\n"),
        "both `run-output` and `stdout` are given"
    );
    assert_eq!(
        reason("//~ exit: 1\n//~ panic: bounds\n"),
        "a test that expects a panic must exit with status 101"
    );
    assert_eq!(
        reason("//~ exit: 1\nf() //~ ERROR E0001\n"),
        "a test of a program with errors must exit with status 2"
    );
    assert_eq!(
        reason("//~ panic: bounds\n//~ exit: 101\nf() //~ ERROR E0001\n"),
        "a test of a program with errors must exit with status 2"
    );
    assert_eq!(
        reason("//~ exit: 2\n//~ stderr:\n//~ | x\nf() //~ ERROR E0001\n"),
        "a test that expects status 2 can't have a `stderr` block"
    );
    assert_eq!(
        reason("f() //~ ERROR E0001\ntest \"t\" {} //~ PASS\n"),
        "a test with errors can't have `PASS` or `FAIL` entries"
    );
    assert_eq!(
        reason("//~ stdin: \"\"\ntest \"t\" {} //~ PASS\n"),
        "a test-block test can't have run keys"
    );
}

#[test]
fn header_annotations_end_with_the_header_region() {
    let error = spec("fn main() {}\n//~ exit: 1\n").unwrap_err();
    assert_eq!(error.line, Some(2));
    assert_eq!(error.reason, "an annotation line after the header region");
    assert!(spec("// a comment\n\n//~ exit: 1\nfn main() {}\n").is_ok());
}

#[test]
fn header_annotations_live_only_in_the_header_file() {
    let files = [
        SourceFile {
            path: "main.lt".to_owned(),
            text: "fn main() {}\n".to_owned(),
        },
        SourceFile {
            path: "util.lt".to_owned(),
            text: "//~ exit: 1\n".to_owned(),
        },
    ];
    let error = parse(&files, "main.lt").unwrap_err();
    assert_eq!(error.file, "util.lt");
    assert_eq!(error.reason, "header annotations belong in `main.lt`");
}

#[test]
fn inline_annotations_record_their_file() {
    let files = [
        SourceFile {
            path: "main.lt".to_owned(),
            text: "fn main() {}\n".to_owned(),
        },
        SourceFile {
            path: "a/b.lt".to_owned(),
            text: "\nfn f() {} //~ ERROR E0001\n".to_owned(),
        },
    ];
    let spec = parse(&files, "main.lt").unwrap();
    assert_eq!(spec.diagnostics[0].to_string(), "E0001 at a/b.lt:2");
}
