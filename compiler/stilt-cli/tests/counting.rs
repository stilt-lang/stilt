//! Reference counting where a local could borrow what it reads (goals debug-speed and no-leaks):
//! a local borrows only while nothing can release or change what it reads, so each program
//! here prints what value semantics says, and ends with every count at zero,
//! both under `stilt run` and as an executable that `stilt build` writes.

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};

/// Runs `source` under `stilt run` with its MIR written out, then as a built executable, checks
/// that both print `expected` and succeed, and returns the MIR.
fn runs_as(name: &str, source: &str, expected: &str) -> String {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("counting")
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
    succeeds(&run, expected, "stilt run");
    let exe = dir.join("program");
    let built = Command::new(stilt)
        .arg("build")
        .arg("-o")
        .arg(&exe)
        .arg(&file)
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    let ran = Command::new(&exe).output().expect("the program runs");
    succeeds(&ran, expected, "the executable");
    mir
}

/// The lines of the MIR of the function `name`.
fn body<'m>(mir: &'m str, name: &str) -> Vec<&'m str> {
    let start = format!("fn {name}(");
    mir.lines()
        .skip_while(|l| !l.starts_with(&start))
        .take_while(|l| *l != "}")
        .collect()
}

fn succeeds(output: &Output, expected: &str, what: &str) {
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        expected,
        "{what}: {}",
        String::from_utf8_lossy(&output.stderr)
            .lines()
            .take(20)
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(output.status.success(), "{what}: {output:?}");
}

#[test]
fn an_element_read_before_its_list_is_written_keeps_its_value() {
    let source = "fn main() / io {\n  var xs = [\"a{1}\", \"b{2}\"]\n  let x = xs[0]\n  xs[0] = \"c{3}\"\n  print(\"{x} {xs[0]}\")\n}\n";
    runs_as("written", source, "a1 c3\n");
}

#[test]
fn an_element_read_before_its_list_grows_keeps_its_value() {
    let source = "fn main() / io {\n  var xs = [\"a{1}\"]\n  let x = xs[0]\n  for i in 0..100 { xs.push(\"n{i}\") }\n  print(\"{x} {xs.len()}\")\n}\n";
    runs_as("grows", source, "a1 101\n");
}

#[test]
fn a_field_read_before_its_record_is_replaced_keeps_its_value() {
    let source = "type P = { name: str }\n\nfn main() / io {\n  var p = P { name: \"n{1}\" }\n  let n = p.name\n  p = P { name: \"m{2}\" }\n  print(\"{n} {p.name}\")\n}\n";
    runs_as("replaced", source, "n1 m2\n");
}

#[test]
fn an_element_of_a_temporary_list_outlives_it() {
    let source = "fn words() -> List<str> { [\"w{1}\", \"w{2}\"] }\n\nfn main() / io {\n  let w = words()[1]\n  let v = words()[0]\n  print(\"{w} {v}\")\n}\n";
    runs_as("temporary", source, "w2 w1\n");
}

#[test]
fn a_borrowed_element_moved_into_a_record_is_counted() {
    let source = "type Box = { v: str }\n\nfn main() / io {\n  var xs = [\"a{1}\"]\n  let b = Box { v: xs[0] }\n  xs = []\n  print(\"{b.v} {xs.len()}\")\n}\n";
    runs_as("moved", source, "a1 0\n");
}

#[test]
fn reads_through_an_inout_list_of_records_see_each_write() {
    let source = "type C = { n: i64, s: str }\n\nfn bump(inout cs: List<C>) {\n  for i in 0..cs.len() {\n    let before = cs[i].s\n    cs[i].n += cs[i].n + 1\n    cs[i].s = \"{before}!\"\n  }\n}\n\nfn main() / io {\n  var cs = [C { n: 1, s: \"x{1}\" }, C { n: 2, s: \"y{2}\" }]\n  let kept = cs\n  bump(inout cs)\n  bump(inout cs)\n  print(\"{cs[0].n} {cs[0].s} {cs[1].n} {cs[1].s} {kept[0].s}\")\n}\n";
    runs_as("inout", source, "7 x1!! 11 y2!! x1\n");
}

#[test]
fn a_match_on_an_element_of_a_borrowed_list_reads_what_its_patterns_bind() {
    let source = "fn total(xs: List<Option<str>>) -> i64 {\n  var n = 0\n  for i in 0..xs.len() {\n    match xs[i] {\n      Some(s) => { n += s.len() }\n      None => {}\n    }\n  }\n  n\n}\n\nfn main() / io {\n  print(\"{total([Some(\"a{1}\"), None, Some(\"bc{2}\")])}\")\n}\n";
    runs_as("matched", source, "5\n");
}

#[test]
fn the_length_of_an_inout_list_is_read_as_it_grows() {
    let source = "fn fill(inout xs: List<str>, n: i64) {\n  while xs.len() < n { xs.push(\"x{xs.len()}\") }\n}\n\nfn main() / io {\n  var xs = []\n  fill(inout xs, 3)\n  print(\"{xs.len()} {xs[2]}\")\n}\n";
    runs_as("length", source, "3 x2\n");
}

#[test]
fn a_list_read_before_a_call_that_replaces_it_keeps_its_value() {
    // The `let` argument is read before the call starts, which empties the list (modes.durations).
    let source = "fn take(inout xs: List<str>, old: List<str>) -> i64 {\n  xs = []\n  old.len()\n}\n\nfn main() / io {\n  var xs = [\"a{1}\", \"b{2}\"]\n  let n = take(inout xs, xs)\n  print(\"{n} {xs.len()}\")\n}\n";
    runs_as("replaced-in-call", source, "2 0\n");
}

#[test]
fn a_copy_of_a_list_variable_outlives_its_growth() {
    let source = "fn main() / io {\n  var xs = [\"a{1}\"]\n  let ys = xs\n  xs.push(\"b{2}\")\n  xs[0] = \"c{3}\"\n  print(\"{ys.len()} {ys[0]} {xs[0]}\")\n}\n";
    runs_as("copy", source, "1 a1 c3\n");
}

const GROWN: &str =
    "fn grown(xs: List<i64>) -> List<i64> {\n  var ys = xs\n  ys.push(9)\n  ys\n}\n\n";

/// The statements of `main` that copy a local, in the MIR.
fn copies(mir: &str) -> Vec<&str> {
    body(mir, "main.main")
        .into_iter()
        .filter(|l| l.trim_start().starts_with("dup "))
        .collect()
}

#[test]
fn a_variable_in_memory_is_handed_over_at_its_last_use() {
    // `push` takes a pointer to `xs`, so it lives in memory; its last use gives the callee the
    // reference (values.passing-values), and the callee grows it in place.
    let main = "fn main() / io {\n  var xs = [1, 2, 3]\n  xs.push(4)\n  let zs = grown(xs)\n  print(\"{zs.len()}\")\n}\n";
    let mir = runs_as("handed", &format!("{GROWN}{main}"), "5\n");
    assert_eq!(copies(&mir), Vec::<&str>::new(), "{mir}");
}

#[test]
fn a_variable_in_memory_read_after_the_call_is_copied() {
    let main = "fn main() / io {\n  var xs = [1, 2, 3]\n  xs.push(4)\n  let zs = grown(xs)\n  print(\"{xs.len()} {zs.len()} {xs[3]} {zs[4]}\")\n}\n";
    let mir = runs_as("copied_after", &format!("{GROWN}{main}"), "4 5 4 9\n");
    assert_eq!(copies(&mir).len(), 1, "{mir}");
}

#[test]
fn a_variable_in_memory_that_the_call_replaces_is_handed_over() {
    let main = "fn main() / io {\n  var xs = [1]\n  for i in 0..3 {\n    xs.push(i)\n    xs = grown(xs)\n  }\n  print(\"{xs}\")\n}\n";
    let mir = runs_as(
        "handed_again",
        &format!("{GROWN}{main}"),
        "[1, 0, 9, 1, 9, 2, 9]\n",
    );
    assert_eq!(copies(&mir), Vec::<&str>::new(), "{mir}");
}

#[test]
fn a_variable_in_memory_passed_by_pointer_after_the_call_is_copied() {
    let source = "fn grown(xs: List<i64>) -> List<i64> {\n  var ys = xs\n  ys.push(9)\n  ys\n}\n\nfn fill(inout xs: List<i64>) { xs.push(7) }\n\nfn main() / io {\n  var xs = [1]\n  let zs = grown(xs)\n  fill(inout xs)\n  print(\"{xs} {zs}\")\n}\n";
    let mir = runs_as("copied_pointer", source, "[1, 7] [1, 9]\n");
    assert_eq!(copies(&mir).len(), 1, "{mir}");
}
