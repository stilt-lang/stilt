//! `stilt build`: a program built into an executable runs as `stilt run` runs it, with its
//! arguments, its output and its exit status (program.exit-statuses and program.panic-report), and
//! builds for every target from either host (goal targets and cross-compilation). The conformance
//! suite runs through built executables too, with `just run`, and across the matrix of hosts and
//! targets with `just cross`. A build is the same byte for byte whatever the number of threads that
//! compile it (goal clean-debug-build), and whatever code an engine kept from the builds before it
//! (goal compile-time-code-rebuilds).

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

mod common;

/// Builds `source`, written to a file of its own, and returns the build's output and the
/// executable.
fn build(name: &str, source: &str) -> (Output, PathBuf) {
    build_with(name, source, &[])
}

/// As [`build`], with more arguments for `stilt build`.
fn build_with(name: &str, source: &str, args: &[&str]) -> (Output, PathBuf) {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("build")
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    fs::write(dir.join("main.lt"), source).expect("the program can be written");
    let exe = dir.join("program");
    let output = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .arg("build")
        .args(args)
        .arg("-o")
        .arg(&exe)
        .arg(dir.join("main.lt"))
        .output()
        .expect("stilt runs");
    (output, exe)
}

fn run(exe: &PathBuf, args: &[&str]) -> Output {
    Command::new(exe)
        .args(args)
        .output()
        .expect("the program runs")
}

#[test]
fn a_built_program_prints_and_reads_its_arguments() {
    let source = "use std.cli\n\nfn main() / io {\n  let xs = [3, 1, 2].sorted()\n  print(\"{xs} {cli.args()}\")\n}\n";
    let (built, exe) = build("args", source);
    assert!(built.status.success(), "{built:?}");
    let output = run(&exe, &["a", "b c"]);
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "[1, 2, 3] [\"a\", \"b c\"]\n"
    );
}

/// A build leaves the executable and, for macOS when `dsymutil` is installed, the bundle of its
/// debug information, but no object.
#[test]
fn a_build_leaves_only_the_executable_and_its_debug_information() {
    let (built, exe) = build("alone", "fn main() {}\n");
    assert!(built.status.success(), "{built:?}");
    let mut names: Vec<String> = fs::read_dir(exe.parent().expect("a directory"))
        .expect("the directory can be read")
        .map(|e| {
            e.expect("an entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    names.sort();
    let dsymutil = Command::new("dsymutil").arg("--version").output().is_ok();
    if cfg!(target_os = "macos") && dsymutil {
        assert_eq!(names, ["main.lt", "program", "program.dSYM"]);
    } else {
        assert_eq!(names, ["main.lt", "program"]);
    }
}

#[test]
fn a_built_program_panics_with_the_report_and_status_of_dr_006() {
    let source =
        "fn main() / io {\n  print(\"before\")\n  let xs = [1, 2]\n  print(\"{xs[5]}\")\n}\n";
    let (built, exe) = build("panic", source);
    assert!(built.status.success(), "{built:?}");
    let output = run(&exe, &[]);
    assert_eq!(output.status.code(), Some(101));
    assert_eq!(String::from_utf8_lossy(&output.stdout), "before\n");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.starts_with("panic: bounds: "), "{stderr}");
    assert!(stderr.contains("  at main.lt:4:11"), "{stderr}");
}

#[test]
fn an_error_that_escapes_main_ends_with_status_1() {
    let source = "type Oops = | Oops\n\nfn main() / {io, raise<Oops>} {\n  raise Oops\n}\n";
    let (built, exe) = build("raise", source);
    assert!(built.status.success(), "{built:?}");
    let output = run(&exe, &[]);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(String::from_utf8_lossy(&output.stderr), "error: Oops\n");
}

#[test]
fn a_program_with_errors_isnt_built() {
    let (built, exe) = build("errors", "fn main() / io {\n  print(1)\n}\n");
    assert_eq!(built.status.code(), Some(2));
    assert!(!exe.exists());
    assert!(String::from_utf8_lossy(&built.stderr).contains("E0311"));
}

/// A program built for each target is an executable of the target's format and machine.
#[test]
fn a_program_builds_for_every_target() {
    let source = "fn main() / io {\n  print(\"hello\")\n}\n";
    let (built, exe) = build_with("macos", source, &["--target", "aarch64-macos"]);
    assert!(built.status.success(), "{built:?}");
    let bytes = fs::read(&exe).expect("the executable can be read");
    // A 64-bit Mach-O file, little-endian, for arm64.
    assert_eq!(bytes[..4], [0xcf, 0xfa, 0xed, 0xfe]);
    assert_eq!(bytes[4..8], [0x0c, 0x00, 0x00, 0x01]);

    let (built, exe) = build_with("linux", source, &["--target", "x86_64-linux"]);
    assert!(built.status.success(), "{built:?}");
    let bytes = fs::read(&exe).expect("the executable can be read");
    // A 64-bit ELF executable, little-endian, for x86-64, static: no interpreter.
    assert_eq!(bytes[..4], *b"\x7fELF");
    assert_eq!(bytes[4..6], [2, 1]);
    assert_eq!(u16::from_le_bytes([bytes[18], bytes[19]]), 62);
    assert!(!bytes.windows(13).any(|w| w == b"/lib64/ld-lin"));

    let (built, exe) = build_with("linux-arm", source, &["--target", "aarch64-linux"]);
    assert!(built.status.success(), "{built:?}");
    let bytes = fs::read(&exe).expect("the executable can be read");
    // A 64-bit ELF executable, little-endian, for aarch64, static: no interpreter.
    assert_eq!(bytes[..4], *b"\x7fELF");
    assert_eq!(bytes[4..6], [2, 1]);
    assert_eq!(u16::from_le_bytes([bytes[18], bytes[19]]), 183);
    assert!(!bytes.windows(8).any(|w| w == b"/lib/ld-"));
}

#[test]
fn an_unknown_target_is_refused() {
    let (built, exe) = build_with("unknown", "fn main() {}\n", &["--target", "riscv64-linux"]);
    assert_eq!(built.status.code(), Some(2));
    assert!(!exe.exists());
    let stderr = String::from_utf8_lossy(&built.stderr);
    // wasm32-wasip1 is a target of `stilt build` (wasm.target).
    assert!(
        stderr.contains(
            "the targets are aarch64-macos, x86_64-linux, aarch64-linux and wasm32-wasip1"
        ),
        "{stderr}"
    );
}

#[test]
fn a_build_is_the_same_whatever_the_number_of_threads() {
    // Enough functions that Cranelift compiles them on several threads.
    let mut source = String::from("fn step0(n: i64) -> i64 { n }\n");
    for i in 1..200 {
        let prev = i - 1;
        writeln!(
            source,
            "fn step{i}(n: i64) -> i64 {{ if n % {i} == 0 {{ step{prev}(n + 1) }} else {{ step{prev}(n) * 2 % 1000 }} }}"
        )
        .expect("a string takes text");
    }
    source.push_str("fn main() / io {\n  print(\"{step199(7)}\")\n}\n");
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("build")
        .join("threads");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    fs::write(dir.join("main.lt"), &source).expect("the program can be written");
    let built = |threads: &str| {
        let output = Command::new(env!("CARGO_BIN_EXE_stilt"))
            .current_dir(&dir)
            .env("STILT_THREADS", threads)
            .args(["build", "-o", "program", "main.lt"])
            .output()
            .expect("stilt runs");
        assert!(output.status.success(), "{output:?}");
        let exe = fs::read(dir.join("program")).expect("the program was built");
        let ran = run(&dir.join("program"), &[]);
        assert!(ran.status.success(), "{ran:?}");
        (exe, ran.stdout)
    };
    let one = built("1");
    for threads in ["2", "8"] {
        assert!(
            built(threads) == one,
            "{threads} threads built another program"
        );
    }
}

const MAIN: &str = "use shapes\n\nfn main() / io {\n  let all = [shapes.Rect(2, 5), shapes.Square(3)]\n  print(\"{shapes.LABEL} {shapes.total(all)} {shapes.area(shapes.Square(4))}\")\n}\n";
const SHAPES: &str = "pub const LABEL: str = \"area\"\n\npub type Shape = | Square(i64) | Rect(i64, i64)\n\npub fn area(s: Shape) -> i64 {\n  match s {\n    Square(n) => n * n\n    Rect(w, h) => w * h\n  }\n}\n\npub fn total(all: List<Shape>) -> i64 {\n  var sum = 0\n  for s in all { sum += area(s) }\n  sum\n}\n";

/// Whether the directory program at `dir`, built for `target` by way of its engine, is the same
/// executable, byte for byte, as built in a process of its own.
fn same_alone(dir: &Path, target: &str) -> bool {
    build_in(dir, target, false) == build_in(dir, target, true)
}

/// Builds the directory program at `dir` into `program` there, by way of its engine, or in a
/// process of its own when `alone`, for `target`, and gives the executable.
fn build_in(dir: &Path, target: &str, alone: bool) -> Vec<u8> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_stilt"));
    if alone {
        command.env("TMPDIR", common::no_engine());
    }
    let output = command
        .current_dir(dir)
        .args(["build", "--target", target, "-o", "program", "."])
        .output()
        .expect("stilt runs");
    assert!(output.status.success(), "{output:?}");
    fs::read(dir.join("program")).expect("the program was built")
}

/// An engine that builds a program again after each edit reuses the machine code of each
/// function the edit left as it was, and the executable is the one a build in a process of its
/// own writes, byte for byte: after an edit of a body, one that adds a function before the
/// others and a constant, so that the numbers of the functions and data after them move, one
/// that removes them again, and a build for another target in between.
#[test]
fn a_build_after_an_edit_is_the_same_as_a_clean_one() {
    let dir = common::project(
        "build",
        "edits",
        &[("main.lt", MAIN), ("shapes.lt", SHAPES)],
    );
    let host = if cfg!(target_os = "macos") {
        "aarch64-macos"
    } else if cfg!(target_arch = "aarch64") {
        "aarch64-linux"
    } else {
        "x86_64-linux"
    };
    let other = if host == "aarch64-macos" {
        "x86_64-linux"
    } else {
        "aarch64-macos"
    };
    let added = SHAPES.replace(
        "pub fn area(",
        "pub fn first(s: Shape) -> str {\n  match s {\n    Square(_) => \"square\"\n    Rect(_, _) => \"rect\"\n  }\n}\n\npub fn area(",
    );
    let first = MAIN.replace(
        "{shapes.LABEL}",
        "{shapes.first(shapes.Square(1))} {shapes.LABEL}",
    );
    let edits: [(&str, &str, String); 5] = [
        ("shapes.lt", "a body", SHAPES.replace("w * h", "h * w + 0")),
        (
            "shapes.lt",
            "a function added",
            added.replace("w * h", "h * w + 0"),
        ),
        ("main.lt", "a call of it", first),
        (
            "shapes.lt",
            "a constant",
            added.replace("\"area\"", "\"areas\""),
        ),
        ("main.lt", "the call undone", MAIN.to_owned()),
    ];
    assert!(same_alone(&dir, host), "the first builds differ");
    for (file, what, text) in &edits {
        fs::write(dir.join(file), text).expect("the file can be written");
        assert!(same_alone(&dir, host), "after {what}, the builds differ");
        if *what == "a constant" {
            assert!(same_alone(&dir, other), "the builds for {other} differ");
        }
    }
    fs::write(dir.join("shapes.lt"), SHAPES).expect("the file can be written");
    assert!(same_alone(&dir, host), "the last builds differ");
    let ran = run(&dir.join("program"), &[]);
    common::finish(&dir);
    assert_eq!(String::from_utf8_lossy(&ran.stdout), "area 19 16\n");
}

#[test]
fn an_executable_is_written_into_directories_made_for_it_and_never_onto_one() {
    let dir = common::directory("build", "outputs");
    fs::create_dir_all(dir.join("hello")).unwrap();
    fs::write(
        dir.join("hello/main.lt"),
        "fn main() / io { print(\"hi\") }\n",
    )
    .unwrap();
    let stilt = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_stilt"))
            .args(args)
            .current_dir(&dir)
            .output()
            .expect("stilt runs")
    };
    // Beside the program's directory, the default name is the directory's own.
    let refused = stilt(&["build", "hello"]);
    assert_eq!(refused.status.code(), Some(2), "{refused:?}");
    assert!(
        common::stderr(&refused).contains("`hello` is a directory"),
        "{refused:?}"
    );
    let built = stilt(&["build", "hello", "-o", "out/deep/hi"]);
    assert!(built.status.success(), "{built:?}");
    let ran = run(&dir.join("out/deep/hi"), &[]);
    assert_eq!(common::stdout(&ran), "hi\n");
}

/// conformance.load-errors: a path that names no program, or a program with a file that can't be
/// read, ends a command with a message and a status other than 0 and 1.
#[test]
fn a_program_that_cant_be_read_ends_every_command_with_a_message() {
    let dir = common::directory("build", "unreadable");
    fs::create_dir_all(dir.join("stilt.toml")).unwrap();
    for args in [&["check"][..], &["run"], &["test"], &["build", "-o", "x"]] {
        for path in [dir.as_path(), &dir.join("nothing-here")] {
            let out = Command::new(env!("CARGO_BIN_EXE_stilt"))
                .args(args)
                .arg(path)
                .output()
                .expect("stilt runs");
            let status = out.status.code();
            assert!(
                !matches!(status, Some(0 | 1) | None),
                "{args:?} {path:?}: {out:?}"
            );
            assert!(!common::stderr(&out).is_empty(), "{args:?} {path:?}");
        }
    }
}
