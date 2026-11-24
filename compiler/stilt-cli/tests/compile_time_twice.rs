//! Compile-time code gives the same output every time it runs (goal
//! deterministic-compile-time-code): each conformance program of the compile-time tiers, its
//! macros, staging, reflection and procedural macros, is run twice in processes of its own, once
//! with every query on one thread and once on four, and the two runs must end with the same
//! status and print the same output.

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use common::stop_engine;

/// The folders of the conformance suite whose programs run compile-time code.
const FOLDERS: [&str; 4] = ["macros", "staging", "reflection", "procedural"];

/// The programs below `dir`: each `.lt` file outside a directory program, and each directory
/// that holds a `main.lt`.
fn programs(dir: &Path, found: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .expect("a folder of the suite is readable")
        .map(|e| e.expect("an entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            if path.join("main.lt").is_file() {
                found.push(path);
            } else {
                programs(&path, found);
            }
        } else if path.extension().is_some_and(|e| e == "lt") {
            found.push(path);
        }
    }
}

/// `stilt run` of `program` from its folder, with queries on `threads` threads.
fn run(program: &Path, threads: &str) -> Output {
    let dir = program.parent().expect("a program has a folder");
    let output = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .current_dir(dir)
        .env("STILT_THREADS", threads)
        .arg("run")
        .arg(program)
        .stdin(Stdio::null())
        .output()
        .expect("stilt runs");
    if program.is_dir() {
        stop_engine(dir, program);
    }
    output
}

#[test]
fn compile_time_code_gives_the_same_output_on_every_run() {
    let suite = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../conformance");
    let mut found = Vec::new();
    for folder in FOLDERS {
        programs(&suite.join(folder), &mut found);
    }
    assert!(found.len() > 70, "{} programs", found.len());
    let differ: Vec<String> = found
        .iter()
        .filter(|program| {
            let (one, four) = (run(program, "1"), run(program, "4"));
            (one.status.code(), &one.stdout, &one.stderr)
                != (four.status.code(), &four.stdout, &four.stderr)
        })
        .map(|program| program.display().to_string())
        .collect();
    assert!(
        differ.is_empty(),
        "runs that differ:\n{}",
        differ.join("\n")
    );
}
