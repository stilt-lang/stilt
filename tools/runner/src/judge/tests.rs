use std::time::Duration;

use super::*;

fn diagnostic(code: &str, line: usize) -> Diagnostic {
    Diagnostic {
        code: code.to_owned(),
        file: "main.lt".to_owned(),
        line,
    }
}

fn result(line: usize, passed: bool) -> TestResult {
    TestResult {
        file: "main.lt".to_owned(),
        line,
        passed,
    }
}

fn output(code: i32, stdout: &str, stderr: &str) -> Output {
    Output {
        status: Status::Exited(code),
        stdout: stdout.into(),
        stderr: stderr.into(),
    }
}

#[test]
fn diagnostics_match_exactly_in_any_order() {
    let expected = [diagnostic("E0001", 1), diagnostic("W0002", 2)];
    let actual = [diagnostic("W0002", 2), diagnostic("E0001", 1)];
    assert_eq!(diagnostics(&expected, &actual), Vec::<String>::new());
}

#[test]
fn diagnostics_report_missing_and_extra_entries() {
    let expected = [diagnostic("E0404", 3)];
    let actual = [diagnostic("E0404", 4)];
    assert_eq!(
        diagnostics(&expected, &actual),
        [
            "missing E0404 at main.lt:3",
            "unexpected E0404 at main.lt:4"
        ]
    );
}

#[test]
fn diagnostics_count_duplicates() {
    let expected = [diagnostic("E0001", 1), diagnostic("E0001", 1)];
    let actual = [diagnostic("E0001", 1)];
    assert_eq!(
        diagnostics(&expected, &actual),
        ["missing E0001 at main.lt:1"]
    );
}

#[test]
fn a_warning_the_test_doesnt_annotate_fails_it() {
    let actual = [diagnostic("W0101", 2)];
    assert_eq!(diagnostics(&[], &actual), ["unexpected W0101 at main.lt:2"]);
}

#[test]
fn same_check_compares_columns() {
    let placed = |col| Placed {
        code: "E0211".to_owned(),
        file: "main.lt".to_owned(),
        line: 2,
        col,
    };
    assert_eq!(same_check(&[placed(9)], &[placed(9)]), Vec::<String>::new());
    assert_eq!(
        same_check(&[placed(9)], &[placed(8)]),
        [
            "E0211 at main.lt:2:9, not under the other implementation",
            "E0211 at main.lt:2:8 only under the other implementation"
        ]
    );
}

#[test]
fn tests_explain_each_mismatch() {
    let expected = [result(1, true), result(2, false), result(3, true)];
    let actual = [result(1, false), result(2, false), result(4, true)];
    assert_eq!(
        tests(&expected, &actual),
        [
            "the test at main.lt:1 failed, but is marked PASS",
            "no result for the test at main.lt:3",
            "an unexpected test result at main.lt:4",
        ]
    );
}

#[test]
fn run_compares_streams_and_status() {
    let spec = RunSpec {
        stdout: "hi\n".to_owned(),
        ..RunSpec::default()
    };
    assert_eq!(
        run(&spec, &output(0, "hi\n", "ignored")),
        Vec::<String>::new()
    );
    assert_eq!(
        run(&spec, &output(1, "hello\n", "")),
        [
            "exit status 1, expected 0",
            "stdout differs from the expected output"
        ]
    );
}

#[test]
fn same_run_compares_status_and_both_streams() {
    let run = output(0, "hi\n", "note\n");
    assert_eq!(
        same_run(&run, &output(0, "hi\n", "note\n")),
        Vec::<String>::new()
    );
    assert_eq!(
        same_run(&run, &output(101, "ho\n", "")),
        [
            "exit status 0, and 101 under the other implementation",
            "stdout differs from the other implementation's",
            "stderr differs from the other implementation's"
        ]
    );
    assert_eq!(
        same_run(&output(134, "lost", ""), &output(134, "", "")),
        Vec::<String>::new()
    );
}

#[test]
fn same_run_compares_a_panics_detail_only_where_the_reference_fixes_it() {
    let overflow = |detail: &str| {
        output(
            101,
            "",
            &format!("panic: overflow: {detail}\n  at a.lt:3:5\n"),
        )
    };
    assert_eq!(
        same_run(&overflow("out of range"), &overflow("doesn't fit in `u16`")),
        Vec::<String>::new()
    );
    let explicit = |detail: &str| {
        output(
            101,
            "",
            &format!("panic: explicit: {detail}\n  at a.lt:3:5\n"),
        )
    };
    assert_eq!(
        same_run(&explicit("\"a\""), &explicit("\"b\"")),
        ["stderr differs from the other implementation's"]
    );
    let elsewhere = output(101, "", "panic: overflow: out of range\n  at a.lt:4:5\n");
    assert_eq!(
        same_run(&overflow("out of range"), &elsewhere),
        ["stderr differs from the other implementation's"]
    );
}

#[test]
fn alike_runs_compare_status_stdout_and_the_panic_but_not_the_diagnostics() {
    let here = output(
        2,
        "1\n",
        "main.lt:3:1: E0211\npanic: check-error: x\n  at main.lt:2:4\n",
    );
    let there = output(
        2,
        "1\n",
        "error[E0211]\npanic: check-error: y\n  at main.lt:2:4\n",
    );
    assert_eq!(alike_run(&here, &there), Vec::<String>::new());
    let elsewhere = output(2, "1\n", "panic: check-error: y\n  at main.lt:5:4\n");
    assert_eq!(
        alike_run(&here, &elsewhere),
        [
            "a `check-error` panic at main.lt:2:4, and a `check-error` panic at \
             main.lt:5:4 under the other implementation"
        ]
    );
    assert_eq!(
        alike_run(&here, &output(2, "1\n", "")),
        ["a `check-error` panic at main.lt:2:4, and no panic under the other implementation"]
    );
}

#[test]
fn run_checks_stderr_only_when_asked() {
    let spec = RunSpec {
        stderr: Some("oops\n".to_owned()),
        ..RunSpec::default()
    };
    assert_eq!(
        run(&spec, &output(0, "", "")),
        ["stderr differs from the expected output"]
    );
}

#[test]
fn a_panic_report_may_follow_other_stderr_output() {
    let spec = RunSpec {
        exit: 101,
        panic: Some("bounds".to_owned()),
        ..RunSpec::default()
    };
    let stderr = "warning: x\npanic: bounds: index 3, length 2\n  at main.lt:4:7\n";
    assert_eq!(run(&spec, &output(101, "", stderr)), Vec::<String>::new());
    let wrong = "panic: overflow: i64\n  at main.lt:4:7\n";
    assert_eq!(
        run(&spec, &output(101, "", wrong)),
        ["stderr doesn't end with a `bounds` panic report"]
    );
}

#[test]
fn checks_where_a_panic_is_reported() {
    let spec = RunSpec {
        exit: 101,
        panic: Some("bounds".to_owned()),
        panic_at: Some("main.lt:4:7".to_owned()),
        ..RunSpec::default()
    };
    let stderr = "panic: bounds: index 3, length 2\n  at main.lt:4:7\n";
    assert_eq!(run(&spec, &output(101, "", stderr)), Vec::<String>::new());
    let elsewhere = "panic: bounds: index 3, length 2\n  at main.lt:4:8\n";
    assert_eq!(
        run(&spec, &output(101, "", elsewhere)),
        ["the panic isn't reported at main.lt:4:7"]
    );
}

#[test]
fn an_abort_doesnt_compare_stdout() {
    let spec = RunSpec {
        exit: 134,
        ..RunSpec::default()
    };
    assert_eq!(
        run(&spec, &output(134, "partial", "")),
        Vec::<String>::new()
    );
}

#[test]
fn two_runs_that_abort_fail_unless_the_test_expects_it() {
    let (lost, empty) = (output(134, "lost", ""), output(134, "", ""));
    assert_eq!(
        unexpected_abort(&RunSpec::default(), &lost, &empty).as_deref(),
        Some(
            "the program aborted with status 134 under both implementations, which the test doesn't expect"
        )
    );
    let expected = RunSpec {
        exit: 134,
        ..RunSpec::default()
    };
    assert_eq!(unexpected_abort(&expected, &lost, &empty), None);
    let panicked = output(101, "", "");
    assert_eq!(
        unexpected_abort(&RunSpec::default(), &panicked, &panicked),
        None
    );
}

#[test]
fn runs_agree_when_both_pass_the_time_limit() {
    let killed = |stdout: &str| Output {
        status: Status::TimedOut(Duration::from_secs(10)),
        stdout: stdout.into(),
        stderr: Vec::new(),
    };
    assert_eq!(
        same_run(&killed("1\n2\n"), &killed("1\n")),
        Vec::<String>::new()
    );
    assert_eq!(
        alike_run(&killed("1\n2\n"), &killed("1\n")),
        Vec::<String>::new()
    );
    assert_eq!(
        same_run(&killed(""), &output(0, "", "")),
        [
            "the program killed after 10 s on the processor or 120 s in all here, and exited with status 0 under the other implementation"
        ]
    );
}

#[test]
fn a_program_that_doesnt_exit_fails_with_one_reason() {
    let killed = Output {
        status: Status::TimedOut(Duration::from_secs(10)),
        stdout: Vec::new(),
        stderr: Vec::new(),
    };
    assert_eq!(
        run(&RunSpec::default(), &killed),
        ["the program was killed after 10 s on the processor or 120 s in all"]
    );
}

#[test]
fn a_run_that_exits_with_status_0_succeeds() {
    assert_eq!(unsuccessful(&output(0, "", "")), None);
}

#[test]
fn two_runs_that_ran_out_of_memory_alike_fail() {
    assert_eq!(
        unsuccessful(&output(134, "", "")).as_deref(),
        Some(
            "the program exited with status 134 under both implementations, and must exit with status 0"
        )
    );
}
