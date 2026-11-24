//! `stilt build --target wasm32-wasip1`
//! (wasm.target): the natives of `std` through WASI preview 1 (wasm.what-std-reads), the limits and
//! statuses of wasm.limits and wasm.exit-statuses, and the builds of wasm.target, each module run
//! under the wasmtime that `just toolchain` fetches, the reference runtime (wasm.same-meaning).
//! `just cross wasm` runs the conformance suite's run tests as such modules
//! (wasm.conformance-runs).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

mod common;

/// The wasmtime that `compiler/stilt-cli/src/release/wasm.txt` pins.
fn wasmtime() -> PathBuf {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/wasm-tools/wasmtime/wasmtime");
    assert!(
        path.exists(),
        "{} is missing: `just toolchain` fetches it",
        path.display()
    );
    path
}

/// Builds the program at `path` for wasm32-wasip1 into `module`, a release build when `release`.
fn build(path: &Path, module: &Path, release: bool) -> Output {
    let dir = path.parent().expect("a directory");
    let mut command = Command::new(env!("CARGO_BIN_EXE_stilt"));
    command.args(["build", "--target", "wasm32-wasip1", "-o"]);
    command.arg(module).arg(path);
    if release {
        command.arg("--release");
    }
    let built = command
        .env("STILT_HOME", dir.join("home"))
        .env_remove("STILT_CC")
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    built
}

/// Runs `module` in `dir` under wasmtime, with the stack of wasm.limits, a time limit, and
/// `options` before the module and `args` after it, its standard input from `stdin`.
fn run(module: &Path, dir: &Path, options: &[&str], (args, stdin): (&[&str], Stdio)) -> Output {
    Command::new(wasmtime())
        .current_dir(dir)
        .args(["run", "-W", "max-wasm-stack=4194304", "-W", "timeout=30s"])
        .args(options)
        .arg(module)
        .args(args)
        .stdin(stdin)
        .output()
        .expect("wasmtime runs")
}

/// Builds the program `source` as a release build, and runs it with `options` and no input.
fn built_and_run(name: &str, source: &str, options: &[&str]) -> Output {
    let path = common::file("wasm", name, source);
    let dir = path.parent().expect("a directory");
    let module = dir.join("program.wasm");
    build(&path, &module, true);
    run(&module, dir, options, (&[], Stdio::null()))
}

const FILES: &str = "use std.fs\nuse std.io\n\nfn read(path: str) -> str / io {\n  try fs.read(path) catch error because \"the test prints every error\" => \"{error}\"\n}\n\nfn main() / io {\n  print(read(\"data.txt\"))\n  print(read(\"../outside.txt\"))\n  print(read(\"sub/data.txt\"))\n  print(read(\"/data.txt\"))\n}\n";

/// A directory granted as `.` is the module's root too, so `/data.txt` names its `data.txt`
///.
#[test]
fn a_module_reads_the_granted_directories_and_is_refused_the_others() {
    let path = common::file("wasm", "files", FILES);
    let dir = path.parent().expect("a directory");
    fs::write(dir.join("data.txt"), "granted").expect("a file");
    fs::write(dir.join("../outside.txt"), "outside").expect("a file");
    fs::create_dir_all(dir.join("sub")).expect("a directory");
    fs::write(dir.join("sub/data.txt"), "under sub").expect("a file");
    let module = dir.join("files.wasm");
    build(&path, &module, true);
    let ran = run(&module, dir, &["--dir", "."], (&[], Stdio::null()));
    assert_eq!(ran.status.code(), Some(0), "{ran:?}");
    assert_eq!(
        common::stdout(&ran),
        "granted\nPermissionDenied(\"../outside.txt\")\nunder sub\ngranted\n"
    );
    let ran = run(&module, dir, &["--dir", "sub"], (&[], Stdio::null()));
    assert_eq!(ran.status.code(), Some(0), "{ran:?}");
    assert_eq!(
        common::stdout(&ran),
        "PermissionDenied(\"data.txt\")\nPermissionDenied(\"../outside.txt\")\nunder sub\nPermissionDenied(\"/data.txt\")\n"
    );
}

// The protocol doesn't say when stdin arrives, so a poll that gives `None` is asked again for a
// line that the input holds, as the conformance suite's `std/io_poll_line.lt` asks it.
const SYSTEM: &str = "use std.cli\nuse std.clock\nuse std.io\nuse std.random\n\nfn next() -> str / io {\n  loop {\n    match io.poll_line() {\n      Some(line) => return line\n      None => clock.sleep_ms(1)\n    }\n  }\n}\n\nfn main() / io {\n  print(\"{cli.args()} {cli.env(\"STILT_WASM\")} {cli.env(\"STILT_ABSENT\")}\")\n  let start = clock.monotonic_ns()\n  clock.sleep_ms(20)\n  let slept = clock.monotonic_ns() - start\n  print(\"{clock.unix_ms() > 1700000000000} {slept >= 20000000}\")\n  print(\"{random.entropy() != random.entropy()}\")\n  print(next())\n  print(next())\n  print(\"{io.poll_line()}\")\n}\n";

#[test]
fn a_module_reads_its_arguments_environment_clocks_randomness_and_input() {
    let path = common::file("wasm", "system", SYSTEM);
    let dir = path.parent().expect("a directory");
    let module = dir.join("system.wasm");
    build(&path, &module, true);
    fs::write(dir.join("input.txt"), "first\nlast").expect("a file");
    let input = fs::File::open(dir.join("input.txt")).expect("the input opens");
    let options = ["--env", "STILT_WASM=yes"];
    let ran = run(&module, dir, &options, (&["a", "b c"], input.into()));
    assert_eq!(ran.status.code(), Some(0), "{ran:?}");
    assert_eq!(
        common::stdout(&ran),
        "[\"a\", \"b c\"] Some(\"yes\") None\ntrue true\ntrue\nfirst\nlast\nNone\n"
    );
}

const DEPTH: &str = "fn depth(n: i64) -> i64 {\n  if n == 0 { 0 } else { 1 + depth(n - 1) }\n}\n\nfn main() / io {\n  print(\"{depth(10000)}\")\n  print(\"{depth(100000000)}\")\n}\n";

#[test]
fn a_recursion_ten_thousand_calls_deep_runs_and_a_deeper_one_ends_with_134() {
    let ran = built_and_run("depth", DEPTH, &[]);
    assert_eq!(ran.status.code(), Some(134), "{ran:?}");
    assert_eq!(common::stdout(&ran), "10000\n");
}

const FRAMES: &str = "use std.array\n\nfn depth(n: i64) -> i64 {\n  let a: array.Array<i64, 2000> = array.fill(n)\n  if n == 0 { a[0] } else { a[1] - n + 1 + depth(n - 1) }\n}\n\nfn main() / io {\n  print(\"{depth(100)}\")\n  print(\"{depth(1000000)}\")\n}\n";

#[test]
fn a_module_that_finds_its_own_stack_past_its_end_reports_it_and_ends_with_134() {
    let ran = built_and_run("frames", FRAMES, &[]);
    assert_eq!(ran.status.code(), Some(134), "{ran:?}");
    assert_eq!(common::stdout(&ran), "100\n");
    let report = common::stderr(&ran);
    assert!(report.starts_with("fatal: stack overflow\n"), "{report}");
}

const MEMORY: &str = "fn main() / io {\n  var s = \"0123456789abcdef\"\n  var i = 0\n  while i < 40 {\n    s = \"{s}{s}\"\n    i = i + 1\n  }\n  print(\"{s.len()}\")\n}\n";

#[test]
fn a_program_that_allocates_past_four_gibibytes_ends_with_134() {
    let ran = built_and_run("memory", MEMORY, &[]);
    assert_eq!(ran.status.code(), Some(134), "{ran:?}");
    assert_eq!(common::stdout(&ran), "");
    let report = common::stderr(&ran);
    assert!(report.starts_with("fatal: out of memory\n"), "{report}");
}

const EXITS: &str = "use std.cli\n\nfn main() / io {\n  let code = (cli.arg(0) else \"0\").to_i64() else 0\n  print(\"ending with {code}\")\n  exit(code.to_u8() else 0)\n}\n";

/// WASI preview 1's `proc_exit` takes a status below 126, so a program's own larger status
/// ends with 1 under wasmtime, after everything it wrote, but 134, which a trap gives.
#[test]
fn an_exit_status_from_126_up_ends_with_1_but_134() {
    let path = common::file("wasm", "exits", EXITS);
    let dir = path.parent().expect("a directory");
    let module = dir.join("exits.wasm");
    build(&path, &module, true);
    for (code, status) in [("0", 0), ("125", 125), ("126", 1), ("134", 134), ("255", 1)] {
        let ran = run(&module, dir, &[], (&[code], Stdio::null()));
        assert_eq!(ran.status.code(), Some(status), "{ran:?}");
        assert_eq!(common::stdout(&ran), format!("ending with {code}\n"));
    }
}

const HANDLERS: &str = "effect Ask {\n  fn ask(n: i64) -> i64\n}\n\nfn twice() -> i64 / Ask { Ask.ask(1) + Ask.ask(2) }\n\nfn main() / io {\n  let h = handler Ask -> i64 {\n    fn ask(n: i64) -> i64 {\n      print(\"before {n}\")\n      let rest = resume(n * 10)\n      print(\"after {n}\")\n      rest + 1\n    }\n  }\n  print(\"{with h { twice() }}\")\n  let xs = [1, 2, 3]\n  print(\"{xs[3]}\")\n}\n";

#[test]
fn a_build_without_release_runs_as_the_release_build_does() {
    let path = common::file("wasm", "builds", HANDLERS);
    let dir = path.parent().expect("a directory");
    let (fast, slow) = (dir.join("fast.wasm"), dir.join("slow.wasm"));
    build(&path, &fast, true);
    build(&path, &slow, false);
    let (fast, slow) = (
        run(&fast, dir, &[], (&[], Stdio::null())),
        run(&slow, dir, &[], (&[], Stdio::null())),
    );
    assert_eq!(fast.status.code(), Some(101), "{fast:?}");
    assert_eq!(
        common::stdout(&fast),
        "before 1\nbefore 2\nafter 2\nafter 1\n32\n"
    );
    let report = common::stderr(&fast);
    assert!(
        report.starts_with("panic: bounds: ") && report.ends_with("  at main.lt:18:11\n"),
        "{report}"
    );
    assert_eq!(
        (fast.status.code(), &fast.stdout, &fast.stderr),
        (slow.status.code(), &slow.stdout, &slow.stderr)
    );
    for module in [dir.join("fast.wasm"), dir.join("slow.wasm")] {
        let bytes = fs::read(&module).expect("the module reads");
        assert_eq!(imported_modules(&bytes), ["wasi_snapshot_preview1"]);
        assert_eq!(memory_pages(&bytes), Some(65_536));
    }
}

#[test]
fn a_module_is_named_after_its_program_and_no_library_is_built() {
    let path = common::file("wasm", "named", "fn main() / io { print(\"named\") }\n");
    let dir = path.parent().expect("a directory");
    let built = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .current_dir(dir)
        .args(["build", "--target", "wasm32-wasip1", "."])
        .env("STILT_HOME", dir.join("home"))
        .env("TMPDIR", common::no_engine())
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    let module = dir.join("named.wasm");
    let ran = run(&module, dir, &[], (&[], Stdio::null()));
    assert_eq!(common::stdout(&ran), "named\n");
    let lib = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .current_dir(dir)
        .args(["build", "--lib", "--target", "wasm32-wasip1", "."])
        .env("TMPDIR", common::no_engine())
        .output()
        .expect("stilt runs");
    assert_eq!(lib.status.code(), Some(2), "{lib:?}");
    assert!(
        common::stderr(&lib).contains("wasm32-wasip1"),
        "{}",
        common::stderr(&lib)
    );
}

/// The sections of a module, each its id and its bytes.
fn sections(module: &[u8]) -> Vec<(u8, &[u8])> {
    let mut all = Vec::new();
    let mut at = 8;
    while at < module.len() {
        let (size, n) = leb128(&module[at + 1..]);
        let start = at + 1 + n;
        all.push((module[at], &module[start..start + size]));
        at = start + size;
    }
    all
}

/// An unsigned LEB128 number at the start of `bytes`, and how many bytes it takes.
fn leb128(bytes: &[u8]) -> (usize, usize) {
    let mut value = 0;
    for (i, &b) in bytes.iter().enumerate() {
        value |= usize::from(b & 0x7f) << (7 * i);
        if b & 0x80 == 0 {
            return (value, i + 1);
        }
    }
    panic!("a LEB128 number ends")
}

/// A name of an import, its length then its bytes, and the bytes after it.
fn name(bytes: &[u8]) -> (String, &[u8]) {
    let (len, n) = leb128(bytes);
    let end = n + len;
    (
        String::from_utf8_lossy(&bytes[n..end]).into_owned(),
        &bytes[end..],
    )
}

/// The modules a module imports functions from, each once, in order. Its imports are all
/// functions, whose description is a type's index.
fn imported_modules(module: &[u8]) -> Vec<String> {
    let mut modules: Vec<String> = Vec::new();
    for (id, mut section) in sections(module) {
        if id != 2 {
            continue;
        }
        let (count, n) = leb128(section);
        section = &section[n..];
        for _ in 0..count {
            let (from, rest) = name(section);
            let (_, rest) = name(rest);
            assert_eq!(rest[0], 0, "an import of a function");
            let (_, n) = leb128(&rest[1..]);
            section = &rest[1 + n..];
            if !modules.contains(&from) {
                modules.push(from);
            }
        }
    }
    modules
}

/// The most pages of 64 KiB the module's memory may have, if it says.
fn memory_pages(module: &[u8]) -> Option<usize> {
    let (_, section) = sections(module).into_iter().find(|(id, _)| *id == 5)?;
    let flags = section[1];
    let (_, n) = leb128(&section[2..]);
    (flags & 1 == 1).then(|| leb128(&section[2 + n..]).0)
}
