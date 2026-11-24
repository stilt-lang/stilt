//! The standard library inlined into user functions (Values and costs, "A cheap optimizer
//! before Cranelift"; goal debug-speed): a call of a small function of the standard library
//! written in Stilt that is given a closure, and the closure's calls, run in the caller's code,
//! and a program prints, raises and panics as it did, with the same report (program.panic-report),
//! under `stilt run` and as an executable that `stilt build` writes.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// Writes `source` as the program `name`, and returns its file.
fn program(name: &str, source: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("inlining")
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    let file = dir.join("main.lt");
    fs::write(&file, source).expect("the program can be written");
    file
}

/// Runs the program under `stilt run` with its MIR written out, then as a built executable,
/// checks that each exits with `status` and prints `printed`, and returns the MIR and the
/// executable's stderr.
fn runs(file: &Path, status: i32, printed: &str) -> (String, String) {
    let stilt = env!("CARGO_BIN_EXE_stilt");
    let run = Command::new(stilt)
        .arg("run")
        .arg(file)
        .env("STILT_DUMP_MIR", "1")
        .output()
        .expect("stilt runs");
    let mir = String::from_utf8_lossy(&run.stderr).into_owned();
    ended(&run, status, printed, "stilt run");
    let exe = file.with_file_name("program");
    let built = Command::new(stilt)
        .args(["build", "-o"])
        .arg(&exe)
        .arg(file)
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    let ran = Command::new(&exe).output().expect("the program runs");
    ended(&ran, status, printed, "the executable");
    (mir, String::from_utf8_lossy(&ran.stderr).into_owned())
}

fn ended(output: &Output, status: i32, printed: &str, what: &str) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        printed,
        "{what}: {stderr}"
    );
    assert_eq!(output.status.code(), Some(status), "{what}: {stderr}");
}

/// The lines of the function `name` in the MIR.
fn function<'a>(mir: &'a str, name: &str) -> Vec<&'a str> {
    let start = format!("fn {name}(");
    let lines: Vec<&str> = mir
        .lines()
        .skip_while(|l| !l.starts_with(&start))
        .take_while(|l| *l != "}")
        .collect();
    assert!(!lines.is_empty(), "no function {name} in\n{mir}");
    lines
}

/// Checks that `main.main` calls neither the standard library's `callee` nor a closure.
fn inlined(mir: &str, callee: &str) {
    let main = function(mir, "main.main");
    let call = format!("call std.prelude.{callee}(");
    assert!(
        !main.iter().any(|l| l.contains(&call)),
        "{}",
        main.join("\n")
    );
    assert!(
        !main.iter().any(|l| l.contains("= call (")),
        "{}",
        main.join("\n")
    );
}

/// The last two lines of stderr, a panic's report (program.panic-report).
fn report(stderr: &str) -> Vec<&str> {
    let lines: Vec<&str> = stderr.lines().collect();
    lines[lines.len().saturating_sub(2)..].to_vec()
}

// The detail of each report is the runtime's wording, which program.panic-report leaves to the
// implementation.

#[test]
fn a_panic_inside_the_standard_library_from_inlined_code_is_reported_at_the_call() {
    // `map` and its closure run in `main`, and the closure's `slice` of the third word, of one
    // byte, panics with `bounds` (std.str): a panic inside the standard library is located at
    // the call into it, whose callee starts at `w` (program.panic-location).
    let source = "fn main() / io {\n  let words = [\"ab\", \"cd\", \"e\"]\n  print(\"start\")\n  let firsts = words.map(|w| w.slice(0, 2))\n  print(\"never {firsts}\")\n}\n";
    let file = program("std-panic", source);
    let (mir, stderr) = runs(&file, 101, "start\n");
    inlined(&mir, "List.map");
    let expected = [
        "panic: bounds: the range 0..2 is out of bounds for a string of 1 bytes",
        "  at main.lt:4:30",
    ];
    assert_eq!(report(&mir), expected);
    assert_eq!(report(&stderr), expected);
}

#[test]
fn a_panic_inside_an_inlined_closure_is_reported_where_the_closure_panics() {
    // The product of the closure that `map` calls overflows at the third element, located at
    // its left operand.
    let source = "fn main() / io {\n  let xs = [1, 2, 3]\n  let big = 4611686018427387904\n  print(\"start\")\n  let ys = xs.map(|x| x * big)\n  print(\"never {ys}\")\n}\n";
    let file = program("closure-panic", source);
    let (mir, stderr) = runs(&file, 101, "start\n");
    inlined(&mir, "List.map");
    let expected = [
        "panic: overflow: the result is out of range",
        "  at main.lt:5:23",
    ];
    assert_eq!(report(&mir), expected);
    assert_eq!(report(&stderr), expected);
}

#[test]
fn a_raise_through_an_inlined_closure_and_map_reaches_the_callers_catch() {
    let source = "type Odd = { n: i64 }\n\nfn half(x: i64) -> i64 / raise<Odd> {\n  if x % 2 == 1 { raise Odd { n: x } }\n  x / 2\n}\n\nfn halves(xs: List<i64>) -> List<i64> {\n  try xs.map(|x| half(x)) catch e because \"an odd element stops the halving\" => [e.n]\n}\n\nfn main() / io {\n  print(\"{halves([2, 4, 6])} {halves([2, 5, 6])}\")\n}\n";
    let file = program("raise", source);
    let (mir, _) = runs(&file, 0, "[1, 2, 3] [5]\n");
    let halves = function(&mir, "main.halves");
    assert!(
        !halves
            .iter()
            .any(|l| l.contains("call std.prelude.List.map(")),
        "{}",
        halves.join("\n")
    );
}

#[test]
fn records_mapped_filtered_and_folded_through_closures_need_no_box() {
    // The element `map` and `filter` read and lend to their closures, and the record the first
    // closure returns, are read field by field, so no object holds them.
    let source = "type Item = { id: i64, name: str }\n\nfn main() / io {\n  let all = [Item { id: 1, name: \"a\" }, Item { id: 2, name: \"b\" }, Item { id: 3, name: \"c\" }]\n  let up = all.map(|it| Item { id: it.id * 10, name: it.name })\n  let kept = up.filter(|it| it.id != 20)\n  let total = kept.fold(0, |acc, it| acc + it.id)\n  print(\"{total} {kept.len()} {kept[1].name}\")\n}\n";
    let file = program("records", source);
    let (mir, _) = runs(&file, 0, "40 2 c\n");
    inlined(&mir, "List.map");
    inlined(&mir, "List.filter");
    inlined(&mir, "List.fold");
    let main = function(&mir, "main.main");
    let boxes = main.iter().filter(|l| l.contains("= box[")).count();
    let reads = main
        .iter()
        .filter(|l| l.contains("stilt_rt_list_get("))
        .count();
    assert_eq!((boxes, reads), (0, 0), "{}", main.join("\n"));
}

/// Runs the program under `stilt run` and builds it with its MIR written out, and returns the
/// run's stderr and the build's MIR, the executable's stderr and its status, after checking
/// that the run and the executable end alike (goals debug-speed and edit-to-running-program).
fn run_and_built(file: &Path) -> (String, String, String) {
    let stilt = env!("CARGO_BIN_EXE_stilt");
    let run = Command::new(stilt)
        .arg("run")
        .arg(file)
        .output()
        .expect("stilt runs");
    let exe = file.with_file_name("program");
    let built = Command::new(stilt)
        .args(["build", "-o"])
        .arg(&exe)
        .arg(file)
        .env("STILT_DUMP_MIR", "1")
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    let ran = Command::new(&exe).output().expect("the program runs");
    assert_eq!(ran.status.code(), run.status.code());
    assert_eq!(ran.stdout, run.stdout);
    (
        String::from_utf8_lossy(&run.stderr).into_owned(),
        String::from_utf8_lossy(&built.stderr).into_owned(),
        String::from_utf8_lossy(&ran.stderr).into_owned(),
    )
}

#[test]
fn a_panic_inside_an_inlined_user_function_is_reported_where_it_panics() {
    // `scaled` is small and called directly, so a build runs its body in `main`, while a run calls
    // it; its product overflows, located at its left operand, in both (numbers.integer-panics;
    // program.panic-location).
    let source = "fn scaled(x: i64, by: i64) -> i64 {\n  x * by\n}\n\nfn main() / io {\n  print(\"start\")\n  let v = scaled(3, 4611686018427387904)\n  print(\"never {v}\")\n}\n";
    let file = program("user-panic", source);
    let (run, mir, ran) = run_and_built(&file);
    let main = function(&mir, "main.main");
    assert!(
        !main.iter().any(|l| l.contains("call main.scaled(")),
        "{}",
        main.join("\n")
    );
    let expected = [
        "panic: overflow: the result is out of range",
        "  at main.lt:2:3",
    ];
    assert_eq!(report(&run), expected);
    assert_eq!(report(&ran), expected);
}

#[test]
fn a_running_program_keeps_each_user_function_as_a_call() {
    let source =
        "fn twice(x: i64) -> i64 {\n  x + x\n}\n\nfn main() / io {\n  print(\"{twice(21)}\")\n}\n";
    let file = program("user-call", source);
    let (mir, _) = runs(&file, 0, "42\n");
    let main = function(&mir, "main.main");
    assert!(
        main.iter().any(|l| l.contains("call main.twice(")),
        "{}",
        main.join("\n")
    );
}
