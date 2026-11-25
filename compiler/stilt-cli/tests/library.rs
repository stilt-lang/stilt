//! `stilt build --lib` (c.exported-functions and c.static-library): a C
//! program that links a debug or a release library calls its exported functions with each type that
//! C takes (c.exported-signatures), from two threads at once, and sees what they write as they
//! return (c.calls-from-c); a panic ends it with status 101 (c.calls-from-c); the header declares
//! the functions in the order of their modules' paths, with their docs, as C11 and as C++
//! (c.library-header); two release libraries of one program are the same bytes, and a C program
//! can't link two libraries (c.static-library). The C programs are compiled by the system's `cc`.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

mod common;

/// Builds the library `dir/out/NAME` of the program at `path`, with `release` or not.
fn library(path: &Path, dir: &Path, name: &str, release: bool) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_stilt"));
    command.arg("build").arg("--lib");
    if release {
        command.arg("--release");
    }
    let built = command
        .arg("-o")
        .arg(dir.join("out").join(name))
        .arg(path)
        .env("STILT_HOME", dir.join("home"))
        .env_remove("STILT_CC")
        .output()
        .expect("stilt runs");
    common::stop_engine(path, path);
    built
}

/// Compiles and links the C program `source` with the libraries of `dir/out` that `names`
/// name, into `dir/NAME`.
fn link(dir: &Path, program: &str, source: &str, names: &[&str]) -> Output {
    let c = dir.join(format!("{program}.c"));
    fs::write(&c, source).expect("the C program can be written");
    let mut command = Command::new("cc");
    command
        .arg("-o")
        .arg(dir.join(program))
        .arg(&c)
        .arg("-I")
        .arg(dir.join("out"));
    for name in names {
        command.arg(dir.join("out").join(format!("lib{name}.a")));
    }
    // c.static-library: glibc keeps the math library apart from the C library.
    if cfg!(target_os = "linux") {
        command.arg("-lm");
    }
    command.output().expect("cc runs")
}

fn run(exe: &Path) -> Output {
    Command::new(exe).output().expect("the C program runs")
}

const TYPES: &str = "use std.io

/// Adds two integers.
pub extern fn add(a: i64, b: i64) -> i64 {
  a + b
}

pub extern fn mean(a: f64, b: f64) -> f64 {
  (a + b) / 2.0
}

pub extern fn halve(x: f32) -> f32 {
  x / 2.0
}

pub extern fn negate(x: bool) -> bool {
  !x
}

pub extern fn neg8(x: i8) -> i8 {
  -x
}

pub extern fn inc8(x: u8) -> u8 {
  x + 1
}

pub extern fn neg16(x: i16) -> i16 {
  -x
}

pub extern fn inc16(x: u16) -> u16 {
  x + 1
}

pub extern fn neg32(x: i32) -> i32 {
  -x
}

pub extern fn inc32(x: u32) -> u32 {
  x + 1
}

pub extern fn inc64(x: u64) -> u64 {
  x + 1
}

pub extern fn answer() -> i64 {
  42
}

pub extern fn greet() / io {
  print(\"hello\")
}

pub extern fn partial() / io {
  io.write(\"par\")
}
";

const TYPES_C: &str = r#"#include <inttypes.h>
#include <stdio.h>
#include "types.h"

#define SHOW(format, value) (printf(format "\n", value), fflush(stdout))

int main(void) {
  SHOW("%" PRId64, add(40, 2));
  SHOW("%g", mean(2.0, 3.0));
  SHOW("%g", (double)halve(5.0f));
  SHOW("%d", (int)negate(true));
  SHOW("%d", (int)neg8(5));
  SHOW("%u", (unsigned)inc8(254));
  SHOW("%d", (int)neg16(300));
  SHOW("%u", (unsigned)inc16(65534));
  SHOW("%" PRId32, neg32(70000));
  SHOW("%" PRIu32, inc32(4294967294u));
  SHOW("%" PRIu64, inc64(18446744073709551614ull));
  SHOW("%" PRId64, answer());
  greet();
  partial();
  SHOW("%s", "tial");
  return 0;
}
"#;

const TYPES_OUT: &str = "42\n2.5\n2.5\n0\n-5\n255\n-300\n65535\n-70000\n4294967295\n\
                         18446744073709551615\n42\nhello\npartial\n";

#[test]
fn a_c_program_calls_exported_functions_of_each_type_in_debug_and_release_libraries() {
    for release in [false, true] {
        let name = if release {
            "types-release"
        } else {
            "types-debug"
        };
        let dir = common::project("library", name, &[("main.lt", TYPES)]);
        let built = library(&dir, &dir, "types", release);
        assert!(built.status.success(), "{built:?}");
        let linked = link(&dir, "use", TYPES_C, &["types"]);
        assert!(linked.status.success(), "{linked:?}");
        let ran = run(&dir.join("use"));
        assert_eq!(
            common::stdout(&ran),
            TYPES_OUT,
            "release {release}: {ran:?}"
        );
        assert!(ran.status.success());
    }
}

const THREADS: &str = "pub extern fn triangle(n: i64) -> i64 {
  var sum = 0
  var i = 0
  while i < n {
    i += 1
    sum += i
  }
  sum
}
";

const THREADS_C: &str = r#"#include <inttypes.h>
#include <pthread.h>
#include <stdio.h>
#include "threads.h"

static void *call(void *n) {
  int64_t *result = n;
  *result = triangle(*result);
  return NULL;
}

int main(void) {
  int64_t a = 100000, b = 200000;
  pthread_t first, second;
  pthread_create(&first, NULL, call, &a);
  pthread_create(&second, NULL, call, &b);
  pthread_join(first, NULL);
  pthread_join(second, NULL);
  printf("%" PRId64 " %" PRId64 "\n", a, b);
  return 0;
}
"#;

#[test]
fn two_c_threads_call_an_exported_function_at_once() {
    let dir = common::project("library", "threads", &[("main.lt", THREADS)]);
    let built = library(&dir, &dir, "threads", false);
    assert!(built.status.success(), "{built:?}");
    let linked = link(&dir, "use", THREADS_C, &["threads"]);
    assert!(linked.status.success(), "{linked:?}");
    let ran = run(&dir.join("use"));
    assert_eq!(common::stdout(&ran), "5000050000 20000100000\n", "{ran:?}");
}

const PANICS: &str = "pub extern fn third(n: i64) -> i64 / io {
  print(\"before\")
  let xs = [1, 2, 3]
  xs[n]
}
";

const PANICS_C: &str = r#"#include <stdio.h>
#include "panics.h"

int main(void) {
  printf("%lld\n", (long long)third(5));
  return 0;
}
"#;

#[test]
fn a_panic_in_an_exported_function_ends_the_c_program_with_status_101() {
    let dir = common::project("library", "panics", &[("main.lt", PANICS)]);
    let built = library(&dir, &dir, "panics", false);
    assert!(built.status.success(), "{built:?}");
    let linked = link(&dir, "use", PANICS_C, &["panics"]);
    assert!(linked.status.success(), "{linked:?}");
    let ran = run(&dir.join("use"));
    assert_eq!(ran.status.code(), Some(101), "{ran:?}");
    assert_eq!(common::stdout(&ran), "before\n");
    let stderr = common::stderr(&ran);
    let lines: Vec<&str> = stderr.lines().collect();
    assert!(lines.len() >= 2, "{stderr}");
    assert!(
        lines[lines.len() - 2].starts_with("panic: bounds: "),
        "{stderr}"
    );
    assert!(
        lines[lines.len() - 1].starts_with("  at main.lt:4:"),
        "{stderr}"
    );
}

const HEADER: &str = "#ifndef ORDERED_H
#define ORDERED_H

#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern \"C\" {
#endif

// The first of three.
// Its doc goes on.
int64_t first(int64_t n);

double second(double x, bool flag);

void third(void);

#ifdef __cplusplus
}
#endif

#endif
";

#[test]
fn the_header_declares_the_exported_functions_in_order_as_c11_and_cpp() {
    let files = [
        ("main.lt", "pub extern fn third() {}\n"),
        (
            "a.lt",
            "/// The first of three.\n/// Its doc goes on.\n///\n/// Not this paragraph.\npub extern fn first(n: i64) -> i64 {\n  n\n}\n",
        ),
    ];
    let dir = common::project("library", "header", &files);
    fs::create_dir_all(dir.join("b")).expect("a module directory");
    fs::write(
        dir.join("b/c.lt"),
        "pub extern fn second(x: f64, flag: bool) -> f64 {\n  if flag { x } else { 0.0 }\n}\n",
    )
    .expect("a module");
    let built = library(&dir, &dir, "ordered", false);
    assert!(built.status.success(), "{built:?}");
    let header = dir.join("out/ordered.h");
    assert_eq!(fs::read_to_string(&header).expect("a header"), HEADER);
    for (compiler, language) in [("cc", "c"), ("c++", "c++")] {
        let mut command = Command::new(compiler);
        if language == "c" {
            command.arg("-std=c11");
        }
        let checked = command
            .args(["-fsyntax-only", "-Wall", "-Werror", "-x", language])
            .arg(&header)
            .output()
            .expect("the compiler runs");
        assert!(checked.status.success(), "{language}: {checked:?}");
    }
}

#[test]
fn two_release_libraries_of_a_program_are_the_same_bytes() {
    let files = [
        (
            "main.lt",
            "use shapes\n\npub extern fn area(n: i64) -> i64 {\n  shapes.square(n)\n}\n",
        ),
        ("shapes.lt", "pub fn square(n: i64) -> i64 {\n  n * n\n}\n"),
    ];
    let first = common::project("library", "bytes-a", &files);
    let second = common::project("library", "bytes-b", &files);
    let a = library(&first, &first, "shapes", true);
    let b = library(&second, &second, "shapes", true);
    assert!(a.status.success() && b.status.success(), "{a:?} {b:?}");
    let bytes = |dir: &Path| fs::read(dir.join("out/libshapes.a")).expect("a library");
    assert_eq!(bytes(&first), bytes(&second));
}

#[test]
fn a_c_program_that_links_two_stilt_libraries_is_rejected_by_its_linker() {
    let dir: PathBuf = common::directory("library", "two");
    for (name, value) in [("one", 1), ("two", 2)] {
        let program = dir.join(name);
        fs::create_dir_all(&program).expect("a program directory");
        let source = format!("pub extern fn {name}() -> i64 {{\n  {value}\n}}\n");
        fs::write(program.join("main.lt"), source).expect("a program");
        let built = library(&program, &dir, name, false);
        assert!(built.status.success(), "{built:?}");
    }
    let source = "#include <stdio.h>\n#include \"one.h\"\n#include \"two.h\"\n\nint main(void) {\n  printf(\"%lld\\n\", (long long)(one() + two()));\n  return 0;\n}\n";
    let linked = link(&dir, "use", source, &["one", "two"]);
    assert!(!linked.status.success(), "{linked:?}");
    assert!(
        common::stderr(&linked).contains("stilt_runtime_once"),
        "{linked:?}"
    );
}

const DEPTH: &str = "use std.cli

pub extern fn depth(n: i64) -> i64 {
  if n == 0 { 0 } else { 1 + depth(n - 1) }
}

pub extern fn arguments() -> i64 / io {
  cli.args().len()
}
";

const DEPTH_C: &str = r#"#include <inttypes.h>
#include <stdio.h>
#include "depth.h"

int main(int argc, char **argv) {
  printf("%" PRId64 " %" PRId64 "\n", depth(10000), arguments());
  return 0;
}
"#;

#[test]
fn a_call_from_c_has_no_arguments_and_recurses_10000_calls_deep() {
    for release in [false, true] {
        let name = if release {
            "depth-release"
        } else {
            "depth-debug"
        };
        let dir = common::project("library", name, &[("main.lt", DEPTH)]);
        let built = library(&dir, &dir, "depth", release);
        assert!(built.status.success(), "{built:?}");
        let linked = link(&dir, "use", DEPTH_C, &["depth"]);
        assert!(linked.status.success(), "{linked:?}");
        let ran = Command::new(dir.join("use"))
            .args(["a", "b"])
            .output()
            .expect("the C program runs");
        assert_eq!(
            common::stdout(&ran),
            "10000 0\n",
            "release {release}: {ran:?}"
        );
    }
}

#[test]
fn show_marks_an_exported_function() {
    let dir = common::project("library", "show", &[("main.lt", THREADS)]);
    let shown = common::stilt(&["show", "main.triangle", &dir.to_string_lossy()], None);
    common::stop_engine(&dir, &dir);
    let text = common::stdout(&shown);
    // c.exported-fact: `exported` comes first in the bracket, before the inferred facts.
    assert!(
        text.contains("pub extern fn triangle(n: i64) -> i64 [exported"),
        "{text}"
    );
}

/// A library's release build is specialized from its exported functions, its roots, as an
/// executable's is from `main` (builds.specialization).
#[test]
fn a_library_s_instantiations_are_reached_from_its_exports() {
    let source = "pub extern fn larger(a: i64, b: i64) -> i64 {\n  pick(a, b)\n}\n\n\
                  fn pick<T: Ord>(a: T, b: T) -> T {\n  if a > b { a } else { b }\n}\n";
    let dir = common::project("library", "roots", &[("main.lt", source)]);
    let shown = common::stilt(
        &["show", "--release", "main.pick", &dir.to_string_lossy()],
        None,
    );
    common::stop_engine(&dir, &dir);
    let text = common::stdout(&shown);
    assert!(text.contains("compiled for: T = i64"), "{text}");
}
