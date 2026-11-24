//! `std.par` on threads: built programs whose calls run on several threads print what their
//! sequential meaning gives (par.sequential-meaning), run after run, and end with every count back
//! to zero (goal no-leaks), however the threads share what the calls reach: constants first
//! used inside a call, which one thread computes (declarations.constant-evaluation), elements that
//! reach one object, records held inline, a list a closure captures, and calls inside calls. A
//! run that a panic in one part ends keeps its code while another part still runs it.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

/// How many times each executable runs, since threads interleave differently each time.
const RUNS: usize = 20;

/// Builds `source` and runs it [`RUNS`] times, checking that each run prints `expected` and
/// succeeds, which a debug build's check of the counts would fail.
fn runs_as(name: &str, source: &str, expected: &str) {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("par")
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    let file = dir.join("main.lt");
    fs::write(&file, source).expect("the program can be written");
    let exe = dir.join("program");
    let built = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["build", "-o"])
        .arg(&exe)
        .arg(&file)
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    for run in 0..RUNS {
        let ran = Command::new(&exe).output().expect("the program runs");
        assert_eq!(String::from_utf8_lossy(&ran.stdout), expected, "run {run}");
        assert!(ran.status.success(), "run {run}: {ran:?}");
    }
}

/// A list of the integers below `n`, which the programs build with a loop.
const UPTO: &str =
    "fn upto(n: i64) -> List<i64> {\n  var xs = []\n  for i in 0..n { xs.push(i) }\n  xs\n}\n";

#[test]
fn constants_first_used_inside_a_call_are_computed_once() {
    let source = format!(
        "use std.par\n\nconst WEIGHTS: List<i64> = [3, 1, 4, 1, 5, 9, 2, 6]\nconst NAMES: List<str> = [\"a\", \"b\"]\n\nfn main() / io {{\n  let ys = par.map(upto(64), |x| x * WEIGHTS[x % 8])\n  let zs = par.map(upto(64), |x| NAMES)\n  print(\"{{ys[63]}} {{zs[5]}} {{zs.len()}}\")\n}}\n\n{UPTO}"
    );
    // 63 * WEIGHTS[7] is 63 * 6.
    runs_as("constants", &source, "378 [\"a\", \"b\"] 64\n");
}

#[test]
fn objects_that_threads_reach_together_are_counted_atomically() {
    let source = format!(
        "use std.par\n\ntype P = {{ n: i64, s: str }}\n\nfn main() / io {{\n  let a = \"a\"\n  let xs = [a, a, a, a, a, a, a, a]\n  print(\"{{par.map(xs, |x| \"{{x}}!\")}}\")\n  let big = upto(10000).map(|i| \"s{{i}}\")\n  let f = |i: i64| big[i].len() + i\n  print(\"{{par.map(upto(100), f) == par.map(upto(100), f)}}\")\n  var ps = upto(50).map(|i| P {{ n: i, s: \"p{{i}}\" }})\n  let kept = ps\n  par.each(inout ps, |inout p| {{ p.n *= 2 }})\n  print(\"{{ps[49].n}} {{kept[49].n}} {{ps[49].s}}\")\n  print(\"{{par.map(upto(6), |i| par.fold(upto(i * 10), 0, |p, q| p + q))}}\")\n}}\n\n{UPTO}"
    );
    // The sums of 0 up to 10i - 1 are 0, 45, 190, 435, 780 and 1225.
    let expected = "[\"a!\", \"a!\", \"a!\", \"a!\", \"a!\", \"a!\", \"a!\", \"a!\"]\ntrue\n98 49 p49\n[0, 45, 190, 435, 780, 1225]\n";
    runs_as("shared", &source, expected);
}

/// A program that panics in one part of a call of `std.par` while another part still runs.
const PANIC_BESIDE_A_PART: &str = "use std.par\n\nfn spin(n: i64) -> i64 {\n  var acc = 0\n  for i in 0..n { acc = (acc + i * 7) % 1000003 }\n  acc\n}\n\nfn main() / io {\n  let (a, b) = par.both(|| {\n    if spin(10) >= 0 { panic(\"early\") }\n    0\n  }, || spin(30000000))\n  print(\"{a} {b}\")\n}\n";

#[test]
fn a_run_that_a_panic_ends_beside_a_running_part_keeps_its_code_until_the_part_ends() {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("par")
        .join("panic_beside");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    let file = dir.join("main.lt");
    fs::write(&file, PANIC_BESIDE_A_PART).expect("the program can be written");
    for run in 0..5 {
        let ran = Command::new(env!("CARGO_BIN_EXE_stilt"))
            .arg("run")
            .arg(&file)
            .output()
            .expect("stilt runs");
        assert_eq!(ran.status.code(), Some(101), "run {run}: {ran:?}");
        let stderr = String::from_utf8_lossy(&ran.stderr);
        assert!(
            stderr.contains("panic: explicit: \"early\""),
            "run {run}: {stderr}"
        );
    }
}
