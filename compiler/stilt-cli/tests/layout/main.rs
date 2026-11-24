//! Values stored inline (facts.native-allocation; goal inline-values): a value of a type that
//! isn't recursive, a closure, a string, a list or a map is its words, held in locals and passed
//! and returned in registers, so making, matching, destructuring and updating one allocates
//! nothing. A list holds each element in its words, and a scalar narrower than a word in its own
//! width, and a map each key and value. Generic code is compiled for the layouts of its type
//! arguments, whatever their size, and an error of several words comes back in the memory its
//! caller provides, so no value of a fixed size is boxed. Each program prints what value semantics
//! says, makes no box, and ends with every count at zero (no-leaks), both under `stilt run` and as
//! an executable; only polymorphic recursion past the caps of instances makes boxes (`past_caps`).

use std::fs;
use std::path::PathBuf;
use std::process::Command;

mod errors;
mod generics;
mod lists;
mod past_caps;
mod values;

/// Runs `source` under `stilt run` with its MIR written out, then as a built executable, checks
/// that both print `expected`, succeed and make no box, and returns the MIR.
fn runs_as(name: &str, source: &str, expected: &str) -> String {
    let (mir, boxes) = runs_boxing(name, source, expected);
    assert_eq!(boxes, 0, "boxes made by\n{mir}");
    mir
}

/// Runs `source` as [`runs_as`] does, and returns the MIR and the number of boxes it made, the
/// same under `stilt run` as in the executable.
fn runs_boxing(name: &str, source: &str, expected: &str) -> (String, u64) {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("layout")
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
        .env("STILT_COUNTS", "1")
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
    let ran = Command::new(&exe)
        .env("STILT_COUNTS", "1")
        .output()
        .expect("the program runs");
    assert_eq!(String::from_utf8_lossy(&ran.stdout), expected);
    assert!(ran.status.success(), "the executable: {ran:?}");
    let boxes = boxes_made(&mir);
    assert_eq!(boxes, boxes_made(&String::from_utf8_lossy(&ran.stderr)));
    (mir, boxes)
}

/// The number of boxes that a program run with `STILT_COUNTS` reports on stderr.
fn boxes_made(stderr: &str) -> u64 {
    stderr
        .lines()
        .find_map(|l| l.strip_prefix("stilt: boxes "))
        .and_then(|n| n.parse().ok())
        .unwrap_or_else(|| panic!("no count of boxes in\n{stderr}"))
}

/// The lines of the MIR of the function `name`, from its header to its closing brace.
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

/// Checks that the function `name` allocates no object of its own, a box among them.
fn allocates_nothing(mir: &str, name: &str) {
    let lines = body(mir, name);
    assert!(
        lines
            .iter()
            .all(|l| !l.contains("alloc") && !l.contains("= box[")),
        "{}",
        lines.join("\n")
    );
}

/// Checks that the function `name` allocates exactly `n` objects of its own.
fn allocates(mir: &str, name: &str, n: usize) {
    let lines = body(mir, name);
    let count = lines
        .iter()
        .filter(|l| l.contains("= alloc") || l.contains("= box["))
        .count();
    assert_eq!(count, n, "{}", lines.join("\n"));
}

/// Checks that the function `name` counts no new reference to a value.
fn copies_nothing(mir: &str, name: &str) {
    let lines = body(mir, name);
    assert!(
        lines.iter().all(|l| !l.trim_start().starts_with("dup ")),
        "{}",
        lines.join("\n")
    );
}

const P: &str = "type P = { x: i64, y: i64 }\n\n";
