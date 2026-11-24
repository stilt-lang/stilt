//! Lists made unique once (goal debug-speed): a loop that writes a list's elements in every
//! iteration makes the list unique before it, and a write that follows another to the same
//! list, with nothing between that could share it, checks nothing of the list's count, as none
//! does after a list literal or a pop. A list that something shares is still copied before it
//! is written, so each program prints what value semantics says, both under
//! `stilt run` and as an executable that `stilt build` writes, and ends with every count at
//! zero.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

/// Runs `source` under `stilt run` with its MIR written out, then as a built executable, checks
/// that both print `expected` and succeed, and returns the MIR.
fn runs_as(name: &str, source: &str, expected: &str) -> String {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("unique")
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
    let mir = String::from_utf8_lossy(&run.stderr).into_owned();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected, "{mir}");
    assert!(run.status.success(), "stilt run: {mir}");
    let exe = dir.join("program");
    let built = Command::new(stilt)
        .args(["build", "-o"])
        .arg(&exe)
        .arg(&file)
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    let ran = Command::new(&exe).output().expect("the program runs");
    assert_eq!(String::from_utf8_lossy(&ran.stdout), expected);
    assert!(ran.status.success(), "the executable: {ran:?}");
    mir
}

/// How many lines of the function `name` contain each of `calls`.
fn count<const N: usize>(mir: &str, name: &str, calls: [&str; N]) -> [usize; N] {
    let start = format!("fn {name}(");
    let lines: Vec<&str> = mir
        .lines()
        .skip_while(|l| !l.starts_with(&start))
        .take_while(|l| *l != "}")
        .collect();
    assert!(!lines.is_empty(), "no function {name} in\n{mir}");
    calls.map(|call| lines.iter().filter(|l| l.contains(call)).count())
}

/// The making unique, then the writes that check nothing, then those that check the list's count.
const SLOTS: [&str; 3] = ["stilt_rt_unique(", "list_element_at(", "list_slot_at("];

#[test]
fn a_loop_copies_a_shared_list_once_and_writes_the_copy_in_place() {
    let source = "fn scale(inout xs: List<f64>, k: f64) {\n  for i in 0..xs.len() {\n    xs[i] *= k\n    xs[i] += 1.0\n  }\n}\n\nfn main() / io {\n  var xs = [1.0, 2.0, 3.0]\n  let before = xs\n  scale(inout xs, 2.0)\n  scale(inout xs, 10.0)\n  print(\"{before} {xs}\")\n}\n";
    let mir = runs_as("shared", source, "[1.0, 2.0, 3.0] [31.0, 51.0, 71.0]\n");
    // Made unique before the loop, and neither write checks the list's count.
    assert_eq!(count(&mir, "main.scale", SLOTS), [1, 2, 0], "{mir}");
}

#[test]
fn a_loop_that_shares_its_list_in_each_iteration_copies_it_before_each_write() {
    let source = "fn main() / io {\n  var xs = [0, 0, 0]\n  var seen = []\n  for i in 0..xs.len() {\n    xs[i] = i + 1\n    seen.push(xs)\n    xs[i] += 10\n  }\n  print(\"{seen} {xs}\")\n}\n";
    let mir = runs_as(
        "shared-each-time",
        source,
        "[[1, 0, 0], [11, 2, 0], [11, 12, 3]] [11, 12, 13]\n",
    );
    // The push shares the list, so the write after it checks the list's count. That write
    // leaves the list unique, as the literal it starts as is, so the first write of each
    // iteration checks nothing.
    assert_eq!(count(&mir, "main.main", SLOTS), [0, 1, 1], "{mir}");
}

#[test]
fn a_write_after_another_checks_nothing_of_the_lists_count() {
    let source = "fn swap(inout xs: List<i64>, i: i64, j: i64) {\n  let t = xs[i]\n  xs[i] = xs[j]\n  xs[j] = t\n}\n\nfn main() / io {\n  var xs = [1, 2, 3]\n  let ys = xs\n  swap(inout xs, 0, 2)\n  print(\"{ys} {xs}\")\n}\n";
    let mir = runs_as("swap", source, "[1, 2, 3] [3, 2, 1]\n");
    // The reads put both indices in bounds. The first write copies the shared list, and the
    // second writes the copy without checking its count.
    assert_eq!(
        count(&mir, "main.swap", ["list_slot_at(", "list_element_at("]),
        [1, 1],
        "{mir}"
    );
}

#[test]
fn a_loop_that_gives_its_list_to_a_call_writes_it_with_its_check() {
    let source = "fn take(inout xs: List<i64>) -> i64 {\n  xs.pop() else 0\n}\n\nfn drain(inout xs: List<i64>) -> i64 {\n  var total = 0\n  while xs.len() > 1 {\n    xs[0] += 1\n    total += take(inout xs)\n  }\n  total\n}\n\nfn main() / io {\n  var xs = [1, 2, 3, 4]\n  let ys = xs\n  let total = drain(inout xs)\n  print(\"{total} {xs} {ys}\")\n}\n";
    let mir = runs_as("drain", source, "9 [4] [1, 2, 3, 4]\n");
    // `take` takes the list `inout` and might share it, so each iteration's write checks the
    // list's count; its index is in bounds, the element having just been read.
    assert_eq!(count(&mir, "main.drain", SLOTS), [0, 0, 1], "{mir}");
}

#[test]
fn a_loop_that_pops_its_list_makes_it_unique_once() {
    let source = "fn drain(inout xs: List<i64>) -> i64 {\n  var total = 0\n  while xs.len() > 1 {\n    xs[0] += 1\n    total += xs.pop() else 0\n  }\n  total\n}\n\nfn main() / io {\n  var xs = [1, 2, 3, 4]\n  let ys = xs\n  let total = drain(inout xs)\n  print(\"{total} {xs} {ys}\")\n}\n";
    let mir = runs_as("pop", source, "9 [4] [1, 2, 3, 4]\n");
    // `xs.pop()` makes the list unique and shares nothing of it, so the loop makes the list
    // unique once, before it, and its writes check nothing.
    assert_eq!(count(&mir, "main.drain", SLOTS), [1, 1, 0], "{mir}");
}
