//! The bounds checks of element writes that debug builds remove (goal debug-speed): a write
//! whose index facts local to its function prove in bounds still makes its list unique, and
//! checks nothing else, while a write that may be out of bounds keeps its check. So a program
//! panics where and how it did, with the same report (std.lists; program.panic-report), both
//! under `stilt run` and as an executable that `stilt build` writes.

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};

/// Runs `source` under `stilt run` with its MIR written out, then as a built executable,
/// checks that both print `printed` then panic with the two lines of `report`, and returns the
/// MIR.
fn panics_as(name: &str, source: &str, printed: &str, report: [&str; 2]) -> String {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("checks")
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
/// its stderr (program.panic-report), and returns what its stderr held before them.
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

/// How many element slots the function `name` takes for a write, unchecked then checked: each
/// in a list made unique by the write itself or before it.
fn writes(mir: &str, name: &str) -> (usize, usize) {
    let (unchecked, checked) = calls(mir, name, ["list_slot_at(", "stilt_rt_list_slot("]);
    let (unique, unique_checked) = calls(mir, name, ["list_element_at(", "list_element("]);
    (unchecked + unique, checked + unique_checked)
}

/// How many elements the function `name` reads, unchecked then checked.
fn reads(mir: &str, name: &str) -> (usize, usize) {
    calls(mir, name, ["stilt_rt_list_at(", "stilt_rt_list_index("])
}

/// How many lines of the function `name` call each of the two functions `of`.
fn calls(mir: &str, name: &str, of: [&str; 2]) -> (usize, usize) {
    let start = format!("fn {name}(");
    let lines: Vec<&str> = mir
        .lines()
        .skip_while(|l| !l.starts_with(&start))
        .take_while(|l| *l != "}")
        .collect();
    assert!(!lines.is_empty(), "no function {name} in\n{mir}");
    let count = |call: &str| lines.iter().filter(|l| l.contains(call)).count();
    (count(of[0]), count(of[1]))
}

// The detail of each report is the runtime's wording, which program.panic-report leaves to the
// implementation: it names the index and the length of the list whose check failed.

#[test]
fn a_write_past_the_end_of_a_list_panics_where_it_did() {
    let source = "fn shift(inout xs: List<i64>) {\n  for i in 0..xs.len() {\n    xs[i] = 0\n    xs[i + 1] = i\n  }\n}\n\nfn main() / io {\n  var xs = [1, 2, 3]\n  print(\"{xs}\")\n  shift(inout xs)\n  print(\"never\")\n}\n";
    let report = [
        "panic: bounds: index 3 is out of bounds for a list of length 3",
        "  at main.lt:4:5",
    ];
    let mir = panics_as("past-the-end", source, "[1, 2, 3]\n", report);
    // `i` is in bounds where the loop's test has held, and `i + 1` may not be.
    assert_eq!(writes(&mir, "main.shift"), (1, 1), "{mir}");
}

#[test]
fn a_write_past_the_end_in_a_loop_that_prints_panics_where_it_did() {
    let source = "fn scale(inout xs: List<i64>) / io {\n  for i in 0..xs.len() {\n    print(\"{i}: {xs[i]}\")\n    xs[i] = i * 2\n    xs[i + 1] = i\n  }\n}\n\nfn main() / io {\n  var xs = [1, 2, 3]\n  scale(inout xs)\n  print(\"never\")\n}\n";
    let report = [
        "panic: bounds: index 3 is out of bounds for a list of length 3",
        "  at main.lt:5:5",
    ];
    let mir = panics_as("prints", source, "0: 1\n1: 0\n2: 1\n", report);
    // The interpolation pushes onto a list of its own, so the length of `xs` stays known: the
    // read of `xs[i]` and the write to it are unchecked, and `xs[i + 1]` is checked.
    assert_eq!(reads(&mir, "main.scale"), (1, 0), "{mir}");
    assert_eq!(writes(&mir, "main.scale"), (1, 1), "{mir}");
}

#[test]
fn a_write_into_a_list_that_an_element_holds_panics_where_it_did() {
    let source = "fn diagonal(inout g: List<List<i64>>) {\n  for i in 0..g.len() {\n    g[i][i] = 1\n  }\n}\n\nfn main() / io {\n  var g = [[0, 0, 0], [0, 0, 0], [0]]\n  print(\"{g}\")\n  diagonal(inout g)\n  print(\"never\")\n}\n";
    let report = [
        "panic: bounds: index 2 is out of bounds for a list of length 1",
        "  at main.lt:3:5",
    ];
    let mir = panics_as("element", source, "[[0, 0, 0], [0, 0, 0], [0]]\n", report);
    // `i` is in bounds of `g`, and nothing is known of the length of `g[i]`.
    assert_eq!(writes(&mir, "main.diagonal"), (1, 1), "{mir}");
}

#[test]
fn a_write_after_its_list_shrinks_panics_where_it_did() {
    let source = "fn clear(inout xs: List<i64>) {\n  for i in 0..xs.len() {\n    xs[i] = 0\n    let _ = xs.pop()\n  }\n}\n\nfn main() / io {\n  var xs = [1, 2, 3]\n  print(\"{xs}\")\n  clear(inout xs)\n  print(\"never\")\n}\n";
    let report = [
        "panic: bounds: index 2 is out of bounds for a list of length 1",
        "  at main.lt:3:5",
    ];
    let mir = panics_as("shrinks", source, "[1, 2, 3]\n", report);
    // `xs.pop()` takes the list `inout`, so its length is unknown after it.
    assert_eq!(writes(&mir, "main.clear"), (0, 1), "{mir}");
}
