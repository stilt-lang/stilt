//! The checks of integer arithmetic that debug builds prove needless or make cheaper
//! (goal debug-speed): a division by a loop's bound inside the loop checks nothing, an
//! addition of terms at least 0 tests only the sign of its sum, and `if c { x += 1 }` steps `x`
//! by `c` without a branch. Every check that can fail is kept, so a program panics where and how it
//! did, with the same report (numbers.integer-panics; program.panic-report), both under `stilt
//! run` and as an executable that `stilt build` writes.

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};

/// Runs `source` under `stilt run` with its MIR written out, then as a built executable,
/// checks that both print `printed` then panic with the two lines of `report`, and returns the
/// MIR of the function `name`.
fn panics_as(name: &str, source: &str, printed: &str, report: [&str; 2]) -> String {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("arithmetic")
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    let file = dir.join("main.lt");
    fs::write(&file, source).expect("the program can be written");
    let stilt = env!("CARGO_BIN_EXE_stilt");
    let run = Command::new(stilt)
        .arg("run")
        .arg(&file)
        .env("STILT_DUMP_MIR", "1")
        .output()
        .expect("stilt runs");
    let mir = panicked(&run, printed, report, "stilt run");
    let exe = dir.join("program");
    let built = Command::new(stilt)
        .args(["build", "-o"])
        .arg(&exe)
        .arg(&file)
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    let ran = Command::new(&exe).output().expect("the program runs");
    panicked(&ran, printed, report, "the executable");
    mir
}

/// Checks that a run printed `printed`, then panicked with `report` as the last two lines of
/// its stderr, and returns what its stderr held before them.
fn panicked(output: &Output, printed: &str, report: [&str; 2], what: &str) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        printed,
        "{what}: {stderr}"
    );
    assert_eq!(output.status.code(), Some(101), "{what}: {stderr}");
    let lines: Vec<&str> = stderr.lines().collect();
    assert!(lines.ends_with(&report), "{what}: {stderr}");
    lines[..lines.len() - 2].join("\n")
}

/// The lines of the MIR of the function `name`.
fn body<'m>(mir: &'m str, name: &str) -> Vec<&'m str> {
    let start = format!("fn {name}(");
    let lines: Vec<&str> = mir
        .lines()
        .skip_while(|l| !l.starts_with(&start))
        .take_while(|l| *l != "}")
        .collect();
    assert!(!lines.is_empty(), "no function {name} in\n{mir}");
    lines
}

/// How many lines of the function `name` contain `text`.
fn count(mir: &str, name: &str, text: &str) -> usize {
    body(mir, name).iter().filter(|l| l.contains(text)).count()
}

// The detail of each report is the runtime's wording, which program.panic-report leaves to the
// implementation.

#[test]
fn a_division_by_a_loops_bound_checks_nothing_and_one_by_zero_panics() {
    let source = "fn spread(n: i64) -> i64 {\n  var s = 0\n  for i in 0..n { s += i * 7 % n }\n  s + 100 / n\n}\n\nfn main() / io {\n  print(\"{spread(5)}\")\n  print(\"{spread(0)}\")\n}\n";
    let report = [
        "panic: divide-by-zero: division by zero",
        "  at main.lt:4:7",
    ];
    let mir = panics_as("division", source, "30\n", report);
    // `n` is above 0 inside the loop, where `0 <= i < n`, and may be 0 after it.
    assert_eq!(count(&mir, "main.spread", "RemByPositive("), 1, "{mir}");
    assert_eq!(count(&mir, "main.spread", "Div(I64)("), 1, "{mir}");
}

#[test]
fn an_addition_of_terms_at_least_0_panics_where_it_overflows() {
    let source =
        "fn main() / io {\n  for i in 0..3 {\n    print(\"{i + 9223372036854775806}\")\n  }\n}\n";
    let report = [
        "panic: overflow: the result is out of range",
        "  at main.lt:3:13",
    ];
    let mir = panics_as(
        "upward",
        source,
        "9223372036854775806\n9223372036854775807\n",
        report,
    );
    assert_eq!(count(&mir, "main.main", "AddUp(I64)("), 1, "{mir}");
}

#[test]
fn a_step_taken_without_a_branch_panics_where_the_branch_would() {
    let source = "fn count(flags: List<bool>, start: i64) -> i64 {\n  var x = start\n  for i in 0..flags.len() {\n    if flags[i] { x += 1 }\n  }\n  x\n}\n\nfn main() / io {\n  print(\"{count([true, false, true], 0)}\")\n  print(\"{count([true, false, true], 9223372036854775806)}\")\n}\n";
    let report = [
        "panic: overflow: the result is out of range",
        "  at main.lt:4:19",
    ];
    let mir = panics_as("step", source, "2\n", report);
    // The loop's test is the only branch left: the test that ends each iteration is decided,
    // and the step adds the flag itself.
    assert_eq!(count(&mir, "main.count", "if "), 1, "{mir}");
    assert_eq!(count(&mir, "main.count", "Add(I64)("), 1, "{mir}");
}

#[test]
fn a_product_of_sizes_a_branch_bounded_checks_nothing_and_one_past_the_bound_panics() {
    // `n` is between 1 and 3,037,000,499 after the branch, so `n * n` fits in `i64` and checks
    // nothing; `area` multiplies a size that nothing bounds, which still panics.
    let source = "fn cells(n: i64) -> i64 {\n  if n < 1 || n > 3037000499 { return 0 }\n  n * n\n}\n\nfn area(n: i64) -> i64 { n * n }\n\nfn main() / io {\n  print(\"{cells(3037000499)}\")\n  print(\"{area(3037000500)}\")\n}\n";
    let report = [
        "panic: overflow: the result is out of range",
        "  at main.lt:6:26",
    ];
    let mir = panics_as("bounded", source, "9223372030926249001\n", report);
    assert_eq!(count(&mir, "main.cells", "MulWrap(I64)("), 1, "{mir}");
    assert_eq!(count(&mir, "main.area", "Mul(I64)("), 1, "{mir}");
}
