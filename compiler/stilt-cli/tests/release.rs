//! `stilt build --release` (builds.release-builds): a release build runs as the debug build does,
//! panics where it does (builds.same-meaning), refuses a program with an error or a hole
//! (builds.what-it-refuses), names a C compiler that `STILT_CC` names and that can't run
//! (builds.another-compiler), is the same bytes from one directory and one cache to another
//! (builds.same-bytes), compiles again only the files of the modules whose C changed, and maps its
//! code to the program's lines, for macOS and for Linux (builds.line-tables). `just run` builds the
//! conformance suite's run tests as release builds, and `just cross` the Mac's for Linux.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

mod common;

/// Builds the program at `path` into `exe`, with `home` as the cache, and `env` set.
fn release(path: &Path, exe: &Path, home: &Path, env: &[(&str, &str)]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_stilt"));
    command
        .args(["build", "--release", "-o"])
        .arg(exe)
        .arg(path)
        .env("STILT_HOME", home)
        .env_remove("STILT_CC");
    for (k, v) in env {
        command.env(k, v);
    }
    command.output().expect("stilt runs")
}

fn debug(path: &Path, exe: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["build", "-o"])
        .arg(exe)
        .arg(path)
        .output()
        .expect("stilt runs")
}

fn run(exe: &Path, args: &[&str]) -> Output {
    Command::new(exe)
        .args(args)
        .output()
        .expect("the program runs")
}

const PROGRAM: &str = "use std.cli\n\nfn main() / io {\n  let xs = [3, 1, 2].sorted()\n  print(\"{xs} {cli.args()}\")\n  let i = cli.args().len() + 3\n  print(\"{xs[i]}\")\n}\n";

#[test]
fn a_release_build_prints_and_panics_as_the_debug_build_does() {
    let path = common::file("release", "same", PROGRAM);
    let dir = path.parent().expect("a directory");
    let built = release(&path, &dir.join("fast"), &dir.join("home"), &[]);
    assert!(built.status.success(), "{built:?}");
    assert!(debug(&path, &dir.join("slow")).status.success());
    for args in [&["a", "b c"][..], &[]] {
        let (fast, slow) = (run(&dir.join("fast"), args), run(&dir.join("slow"), args));
        assert_eq!(fast.status.code(), Some(101));
        assert_eq!(
            (fast.status.code(), &fast.stdout),
            (slow.status.code(), &slow.stdout)
        );
        let report = String::from_utf8_lossy(&fast.stderr);
        assert!(report.ends_with("  at main.lt:7:11\n"), "{report}");
        assert_eq!(fast.stderr, slow.stderr);
    }
}

#[test]
fn a_release_build_refuses_a_program_with_a_hole() {
    let source = "fn parse(s: str) -> i64 = ?\n\nfn main() / io { print(\"{parse(\"1\")}\") }\n";
    let path = common::file("release", "hole", source);
    let dir = path.parent().expect("a directory");
    let built = release(&path, &dir.join("program"), &dir.join("home"), &[]);
    assert_eq!(built.status.code(), Some(2), "{built:?}");
    let report = String::from_utf8_lossy(&built.stderr);
    assert!(report.contains("[W0300]"), "{report}");
    assert!(report.contains("refuses a program with holes"), "{report}");
    assert!(!dir.join("program").exists());
    assert!(
        debug(&path, &dir.join("debug")).status.success(),
        "a debug build has holes"
    );
}

#[test]
fn a_release_build_refuses_a_program_with_an_error() {
    let path = common::file("release", "error", "fn main() { let x: i64 = \"no\" }\n");
    let dir = path.parent().expect("a directory");
    let built = release(&path, &dir.join("program"), &dir.join("home"), &[]);
    assert_eq!(built.status.code(), Some(2), "{built:?}");
    assert!(String::from_utf8_lossy(&built.stderr).contains("[E0311]"));
    assert!(!dir.join("program").exists());
}

#[test]
fn a_c_compiler_that_cant_run_is_named() {
    let path = common::file("release", "cc", "fn main() {}\n");
    let dir = path.parent().expect("a directory");
    let missing = dir.join("no-such-clang");
    let missing = missing.to_str().expect("a path of UTF-8");
    let built = release(
        &path,
        &dir.join("program"),
        &dir.join("home"),
        &[("STILT_CC", missing)],
    );
    assert_eq!(built.status.code(), Some(2), "{built:?}");
    let report = String::from_utf8_lossy(&built.stderr);
    assert!(
        report.contains(missing) && report.contains("STILT_CC"),
        "{report}"
    );
}

/// The objects in a cache of objects.
fn objects(home: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    for dir in fs::read_dir(home.join("objects"))
        .into_iter()
        .flatten()
        .flatten()
    {
        for o in fs::read_dir(dir.path()).into_iter().flatten().flatten() {
            if o.path().extension().is_some_and(|e| e == "o") {
                found.push(o.path());
            }
        }
    }
    found.sort();
    found
}

#[test]
fn release_builds_are_the_same_bytes_from_any_directory_and_cache() {
    let files = [
        (
            "main.lt",
            "use shapes\n\nfn main() / io { print(\"{shapes.area(3)}\") }\n",
        ),
        ("shapes.lt", "pub fn area(n: i64) -> i64 { n * n }\n"),
    ];
    let first = common::project("release", "bytes-a", &files);
    let second = common::project("release", "bytes-b", &files);
    let a = release(&first, &first.join("program"), &first.join("home"), &[]);
    let b = release(&second, &second.join("program"), &second.join("home"), &[]);
    common::stop_engine(&first, &first);
    common::stop_engine(&second, &second);
    assert!(a.status.success() && b.status.success(), "{a:?} {b:?}");
    let bytes = |dir: &Path| fs::read(dir.join("program")).expect("an executable");
    assert_eq!(bytes(&first), bytes(&second));
    assert_eq!(run(&first.join("program"), &[]).stdout, b"9\n");
}

/// A sum that recurses, which no call inlines, so its module has a file of its own.
fn sum(step: &str) -> String {
    format!(
        "pub fn sum(n: i64) -> i64 {{\n  if n <= 0 {{ 0 }} else {{ {step} + sum(n - 1) }}\n}}\n"
    )
}

#[test]
fn a_build_compiles_again_only_the_modules_whose_c_changed() {
    let (once, twice) = (sum("n"), sum("2 * n"));
    let files = [
        (
            "main.lt",
            "use shapes\n\nfn main() / io { print(\"{shapes.sum(3)}\") }\n",
        ),
        ("shapes.lt", once.as_str()),
    ];
    let dir = common::project("release", "cached", &files);
    let home = dir.join("home");
    assert!(
        release(&dir, &dir.join("program"), &home, &[])
            .status
            .success()
    );
    let before = objects(&home);
    assert_eq!(
        before.len(),
        3,
        "a file per module and program.c: {before:?}"
    );
    fs::write(dir.join("shapes.lt"), twice).expect("the module can be written");
    assert!(
        release(&dir, &dir.join("program"), &home, &[])
            .status
            .success()
    );
    common::stop_engine(&dir, &dir);
    let after = objects(&home);
    assert_eq!(
        after.len(),
        4,
        "only the edited module's object is new: {after:?}"
    );
    assert!(before.iter().all(|o| after.contains(o)));
    assert_eq!(run(&dir.join("program"), &[]).stdout, b"12\n");
}

#[test]
#[cfg(target_os = "macos")]
fn a_release_builds_line_tables_name_the_programs_lines() {
    let path = common::file("release", "lines", PROGRAM);
    let dir = path.parent().expect("a directory");
    assert!(
        release(&path, &dir.join("program"), &dir.join("home"), &[])
            .status
            .success()
    );
    let dwarf = dir.join("program.dSYM/Contents/Resources/DWARF/program");
    // A machine without Xcode's command-line tools has no `dsymutil`, and no debugger.
    let Ok(bytes) = fs::read(dwarf) else { return };
    assert!(bytes.windows(7).any(|w| w == b"main.lt"));
}

/// The Mac builds the release builds of the matrix's Linux machine, which has no published
/// toolchain (builds.release-toolchain), and their executables hold their own line
/// tables. Only they can name the file there: the program's panic report names `main.lt` too,
/// outside them.
#[test]
#[cfg(target_os = "macos")]
fn a_linux_release_builds_line_tables_name_the_programs_lines() {
    use object::{Object as _, ObjectSection as _};

    let path = common::file("release", "linux-lines", PROGRAM);
    let dir = path.parent().expect("a directory");
    let exe = dir.join("program");
    let built = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["build", "--release", "--target", "x86_64-linux", "-o"])
        .arg(&exe)
        .arg(&path)
        .env("STILT_HOME", dir.join("home"))
        .env_remove("STILT_CC")
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    let bytes = fs::read(&exe).expect("an executable");
    let file = object::File::parse(&*bytes).expect("an ELF executable");
    let section = |name: &str| {
        let data = file.section_by_name(name).and_then(|s| s.data().ok());
        data.unwrap_or_default().to_vec()
    };
    let tables = [section(".debug_line"), section(".debug_line_str")].concat();
    assert!(
        tables.windows(7).any(|w| w == b"main.lt"),
        "the line tables name main.lt"
    );
}
