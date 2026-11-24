//! Calling C (c.foreign-functions): a program whose package
//! links zlib builds, as a debug and as a release build, for this machine's own target alone, and
//! is E0612 for another (c.linking and c.build-targets); one that links none calls the C library of
//! any target, WASI's under the wasmtime that `just toolchain` fetches; and a fetched dependency
//! that holds an `unsafe` block needs its entry to grant `unsafe` (c.granting-unsafe); and `stilt
//! show` prints a wrapper's `unsafe` and `foreign` facts (c.unsafe-and-foreign). `just run` runs
//! the conformance suite's tests of the record as built executables, debug and release.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

mod common;
mod repos;

use repos::{Place, codes, message};

const MANIFEST: &str = "[package]\nname = \"zl\"\nlink = [\"z\"]\n";

const CHECKSUM: &str = "use std.c\n\nextern fn crc32(crc: u64, buf: c.Ptr<u8>, len: u32) -> u64\n\n\
                        fn main() / io {\n  let data: List<u8> = [104, 101, 108, 108, 111]\n  \
                        let len = data.len().wrap_to_u32()\n  \
                        let sum = unsafe because \"crc32 reads len bytes of data\" {\n    \
                        data.with_ptr(|p| crc32(0, p, len))\n  }\n  print(\"{sum}\")\n}\n";

/// A directory program, `zl`, that links zlib and prints the CRC-32 of "hello".
fn linking(name: &str) -> PathBuf {
    let dir = common::directory("foreign", name);
    fs::create_dir_all(dir.join("src")).expect("the directory can be made");
    fs::write(dir.join("stilt.toml"), MANIFEST).expect("the manifest can be written");
    fs::write(dir.join("src/main.lt"), CHECKSUM).expect("the program can be written");
    dir
}

/// Builds the program at `path` into `out` with `args`, its cache under `path`'s directory.
fn build(path: &Path, out: &Path, args: &[&str]) -> Output {
    let dir = if path.is_dir() {
        path
    } else {
        path.parent().expect("a directory")
    };
    let built = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .arg("build")
        .args(args)
        .arg("-o")
        .arg(out)
        .arg(path)
        .env("STILT_HOME", dir.join("home"))
        .env_remove("STILT_CC")
        .output()
        .expect("stilt runs");
    common::stop_engine(dir, path);
    built
}

/// A build for another target than this machine's, or for one whose executables load no
/// library, is E0612 at the first library, and writes nothing (c.build-targets).
#[test]
fn a_program_that_links_a_library_builds_for_no_other_target() {
    let dir = linking("other");
    for (target, why) in [
        (
            "x86_64-linux",
            "an executable for x86_64-linux loads no library",
        ),
        (
            "wasm32-wasip1",
            "an executable for wasm32-wasip1 loads no library",
        ),
    ] {
        let out = dir.join(target);
        let built = build(&dir, &out, &["--target", target]);
        assert_eq!(built.status.code(), Some(2), "{built:?}");
        assert!(!out.exists());
        let stderr = String::from_utf8_lossy(&built.stderr);
        let words = stderr.split_whitespace().collect::<Vec<_>>().join(" ");
        let message = format!(
            "This program links the C library `z`, so it builds only for this machine's own \
             target, and {why}:"
        );
        assert!(words.contains(&message), "{stderr}");
        assert!(stderr.contains("stilt.toml:3:9  [E0612]"), "{stderr}");
    }
}

/// On aarch64 macOS, whose executables load libraries, a debug and a release build each name
/// zlib, which they load when they start (c.loading-libraries).
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn a_build_for_this_machine_links_the_library() {
    let dir = linking("own");
    for (name, args) in [("debug", &[][..]), ("release", &["--release"][..])] {
        let exe = dir.join(name);
        let built = build(&dir, &exe, args);
        assert!(built.status.success(), "{built:?}");
        let ran = Command::new(&exe).output().expect("the program runs");
        assert!(ran.status.success(), "{ran:?}");
        assert_eq!(String::from_utf8_lossy(&ran.stdout), "907060870\n");
    }
}

const LENGTH: &str = "use std.c\n\nextern fn strlen(s: c.Str) -> u32\n\nfn main() / io {\n  \
                      let n = unsafe because \"with_c_str ends s with a NUL\" {\n    \
                      \"hello\".with_c_str(|s| strlen(s))\n  }\n  print(\"{n}\")\n}\n";

/// A program that links no library calls `strlen` from WASI's C library, whose `size_t` is 32
/// bits, and from musl's in static x86-64 and aarch64 Linux executables (c.build-targets).
#[test]
fn a_program_that_links_none_calls_the_c_library_of_any_target() {
    let path = common::file("foreign", "strlen", LENGTH);
    let dir = path.parent().expect("a directory");
    let linux = dir.join("linux");
    let built = build(&path, &linux, &["--target", "x86_64-linux"]);
    assert!(built.status.success(), "{built:?}");
    let built = build(
        &path,
        &dir.join("linux-arm"),
        &["--target", "aarch64-linux"],
    );
    assert!(built.status.success(), "{built:?}");
    let module = dir.join("program.wasm");
    let built = build(&path, &module, &["--target", "wasm32-wasip1"]);
    assert!(built.status.success(), "{built:?}");
    let wasmtime =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/wasm-tools/wasmtime/wasmtime");
    let ran = Command::new(wasmtime)
        .args(["run", "-W", "timeout=30s"])
        .arg(&module)
        .output()
        .expect("wasmtime runs");
    assert!(ran.status.success(), "{ran:?}");
    assert_eq!(String::from_utf8_lossy(&ran.stdout), "5\n");
}

const WRAP: &str = "extern fn abs(n: i32) -> i32\n\npub fn magnitude(n: i32) -> i32 {\n  \
                    unsafe because \"abs takes every i32 but the least\" { abs(n) }\n}\n";

/// A fetched dependency whose own code holds an `unsafe` block is E0608 at its entry, which
/// names the function and the block, until the entry grants `unsafe`; `io` doesn't grant it
/// (c.granting-unsafe).
#[test]
fn a_fetched_dependency_with_unsafe_code_needs_the_grant() {
    let place = Place::new("unsafe_grant");
    let repo = place.repo("wrap");
    repo.tag(
        "1.0.0",
        &[
            ("stilt.toml", "[package]\nname = \"wrap\"\n"),
            ("src/main.lt", WRAP),
        ],
    );
    let main = "use wrap\n\nfn main() / io { print(\"{wrap.magnitude(-7)}\") }\n";
    for (may, granted) in [
        ("", false),
        (", may = [\"io\"]", false),
        (", may = [\"unsafe\"]", true),
    ] {
        let entry = format!("wrap = {{ from = \"{}\"{may} }}", repo.url());
        let toml = format!("[package]\nname = \"app\"\n\n[dependencies]\n{entry}\n");
        let app = place.program(&[("stilt.toml", &toml), ("src/main.lt", main)]);
        let checked = place.check("home", &app);
        if granted {
            assert_eq!(codes(&checked), Vec::<String>::new(), "{checked}");
            let ran = place.stilt("home", &["run"], &app);
            assert_eq!(String::from_utf8_lossy(&ran.stdout), "7\n", "{ran:?}");
        } else {
            assert_eq!(codes(&checked), ["E0608"], "{checked}");
            let found = message(&checked, "E0608");
            assert!(
                found.starts_with("`wrap.magnitude` holds an `unsafe` block at "),
                "{found}"
            );
        }
    }
}

const WRAPPER: &str = "use std.c\n\nextern fn crc32(crc: u64, buf: c.Ptr<u8>, len: u32) -> u64\n\n\
                       pub fn checksum(data: List<u8>) -> u64 {\n  \
                       let len = data.len().wrap_to_u32()\n  \
                       unsafe because \"crc32 reads len bytes\" {\n    \
                       data.with_ptr(|p| crc32(0, p, len))\n  }\n}\n\n\
                       pub fn twice(data: List<u8>) -> u64 { checksum(data) * 2 }\n";

/// `stilt show` prints `unsafe` and `foreign` last in a wrapper's bracket, after what a call of C
/// adds (c.effects), the block's reason and the C function on their lines, and neither for its
/// caller, and `show --json` lists both (c.unsafe-and-foreign).
#[test]
fn show_prints_the_unsafe_blocks_and_the_c_functions() {
    let path = common::file("foreign", "show", WRAPPER);
    let shown = common::stilt(
        &["show", "main.checksum", path.to_str().expect("a path")],
        None,
    );
    let text = String::from_utf8_lossy(&shown.stdout);
    assert!(text.starts_with("module main [systems]\n"), "{text}");
    assert!(
        text.contains(
            "pub fn checksum(data: List<u8>) -> u64 [panic, alloc, div, unsafe, foreign: crc32]"
        ),
        "{text}"
    );
    assert!(
        text.contains("// unsafe because \"crc32 reads len bytes\""),
        "{text}"
    );
    assert!(text.contains("`crc32` is C code"), "{text}");
    let caller = common::stilt(
        &["show", "main.twice", path.to_str().expect("a path")],
        None,
    );
    let text = String::from_utf8_lossy(&caller.stdout);
    assert!(
        !text.contains("unsafe") && !text.contains("foreign"),
        "{text}"
    );
    let json = common::stilt(
        &[
            "show",
            "--json",
            "main.checksum",
            path.to_str().expect("a path"),
        ],
        None,
    );
    let value: serde_json::Value = serde_json::from_slice(&json.stdout).expect("JSON");
    assert_eq!(
        value["unsafe"],
        serde_json::json!([{"line": 7, "cause": "unsafe because \"crc32 reads len bytes\""}])
    );
    assert_eq!(
        value["foreign"],
        serde_json::json!([{"line": 8, "cause": "`crc32` is C code", "name": "crc32"}])
    );
}

const TRUSTED: &str = "extern fn labs(n: i64) -> i64 without panic, alloc, div\n\n\
                       pub fn magnitude(n: i64) -> i64 {\n  \
                       unsafe because \"labs takes any i64 but the least\" { labs(n) }\n}\n";

/// A foreign function's `without` clause is trusted: a call of it adds none of what it names, and
/// `stilt show` says so on the call's line, in the order of the `limit` production (c.effects).
#[test]
fn show_says_which_limits_of_c_code_are_trusted() {
    let path = common::file("foreign", "trusted", TRUSTED);
    let shown = common::stilt(
        &["show", "main.magnitude", path.to_str().expect("a path")],
        None,
    );
    let text = String::from_utf8_lossy(&shown.stdout);
    assert!(
        text.contains("pub fn magnitude(n: i64) -> i64 [unsafe, foreign: labs]"),
        "{text}"
    );
    assert!(
        text.contains("`labs` is C code, trusted without panic, alloc, div"),
        "{text}"
    );
}
