//! Large arrays (generics.large-arrays): an array of 65,536 elements, each of a nested array
//! counted, runs under `stilt run` and as an executable that `stilt build` writes, on the
//! program's thread and on a task's, wherever a value can be; its code is the same whatever its
//! size, as a loop or a copy over its memory; a frame of one past the end of the stack ends the
//! run as a stack overflow does (program.exit-statuses); and so does a function that would hold
//! one past both what compiled code holds and what generics.large-arrays asks for, as running out
//! of memory does. Each run ends with every count back to
//! zero, which a debug build's check at exit would fail otherwise (goal no-leaks).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use object::{Object, ObjectSection, ObjectSymbol};

/// Writes `source` as a program of its own directory, and gives its file.
fn program(name: &str, source: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("large_arrays")
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    let file = dir.join("main.lt");
    fs::write(&file, source).expect("the program can be written");
    file
}

/// Builds the program `file` into an executable beside it, and gives the executable.
fn build(file: &Path) -> PathBuf {
    let exe = file.with_file_name("program");
    let built = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["build", "-o"])
        .arg(&exe)
        .arg(file)
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    exe
}

/// The program's run with `stilt run`, then the run of the executable `stilt build` writes.
fn runs(file: &Path) -> [Output; 2] {
    let ran = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .arg("run")
        .arg(file)
        .output()
        .expect("stilt runs");
    let executed = Command::new(build(file))
        .output()
        .expect("the program runs");
    [ran, executed]
}

/// Checks that both runs of `file` print `expected` and succeed.
fn prints(file: &Path, expected: &str) {
    for (how, out) in ["run", "build"].iter().zip(runs(file)) {
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            expected,
            "{how}: {out:?}"
        );
        assert!(out.status.success(), "{how}: {out:?}");
    }
}

/// The bytes of machine code of the program's own functions in an executable, those the
/// compiler names `stilt_` and a number, apart from the runtime's: each symbol of the text
/// section runs to the next one.
fn program_code(exe: &Path) -> u64 {
    let data = fs::read(exe).expect("the executable is readable");
    let file = object::File::parse(&*data).expect("the executable parses");
    let text = file
        .section_by_name("__text")
        .or_else(|| file.section_by_name(".text"))
        .expect("the executable has code");
    let mut starts: Vec<(u64, bool)> = file
        .symbols()
        .filter(|s| s.section_index() == Some(text.index()))
        .map(|s| {
            let name = s.name().unwrap_or_default().trim_start_matches('_');
            let numbered = name
                .strip_prefix("stilt_")
                .is_some_and(|rest| rest.starts_with(|c: char| c.is_ascii_digit()));
            (s.address(), numbered)
        })
        .collect();
    starts.sort_unstable();
    starts.dedup_by_key(|(at, _)| *at);
    let end = text.address() + text.size();
    let ends = starts.iter().skip(1).map(|(at, _)| *at).chain([end]);
    starts
        .iter()
        .zip(ends)
        .filter(|((_, numbered), _)| *numbered)
        .map(|((at, _), next)| next - at)
        .sum()
}

/// A program that makes, copies, passes, returns, reads, writes, compares, shows, lists and
/// maps arrays of `N` elements, and holds them in a record and a closure.
const SIZED: &str = r#"use std.array

const N: i64 = SIZE

type Box = { cells: array.Array<i64, N>, name: str }

fn total(a: array.Array<i64, N>) -> i64 {
  var s = 0
  for x in a { s += x }
  s
}

fn ramp() -> array.Array<i64, N> {
  var a: array.Array<i64, N> = array.fill(0)
  for i in 0..N { a[i] = i }
  a
}

fn main() / io {
  let r = ramp()
  var c = r
  c[0] = 7
  let b = Box { cells: c, name: "b" }
  let words: array.Array<str, N> = array.fill("ab")
  let d = r.map(|x| x * 2)
  let at = |i: i64| r[i] + b.cells[i]
  let back: Option<array.Array<i64, N>> = array.from_list(r.to_list())
  let [first, ..] = c
  let shown = "{r}"
  print("{total(r)} {total(d)} {at(1)} {first} {r == c} {r < c} {back == Some(r)}")
  print("{words[N - 1]} {shown.len() > 0} {b.name}")
}
"#;

#[test]
fn an_array_s_code_is_the_same_whatever_its_size() {
    // generics.large-arrays: the sum of `0..n` is n(n - 1)/2, and of its doubles twice that.
    let small = program("sized_64", &SIZED.replace("SIZE", "64"));
    prints(&small, "2016 4032 2 7 false true true\nab true b\n");
    let large = program("sized_65536", &SIZED.replace("SIZE", "65_536"));
    prints(
        &large,
        "2147450880 4294901760 2 7 false true true\nab true b\n",
    );
    let (small, large) = (program_code(&build(&small)), program_code(&build(&large)));
    assert!(small > 0, "the program's functions are found");
    assert!(
        large <= 2 * small,
        "65,536 elements compile to {large} bytes of code, 64 to {small}"
    );
}

#[test]
fn large_arrays_run_wherever_a_value_can_be() {
    // generics.arrays and generics.large-arrays, on 65,536 elements: in a record, a variant, a
    // tuple, an option, a closure, a list, a map's values and keys, an operation's arguments
    // (handlers.performing-operation), a reflected value (meta.fresh-types) and a task
    // (tasks.scopes), and of strings, whose counts each copy shares; the sum of `0..65_536` is
    // 2,147,450,880.
    let source = include_str!("large_arrays/positions.lt");
    let small = (0..20).map(|_| "3").collect::<Vec<_>>().join(", ");
    let expected = format!(
        "2147450880 2147450888 65535 65536 7\ng 1 2147450880\n2 131071\n65536 true true\n\
         131070 4294901760\n0 1 1\n131073 0 ab\n2 9 7 2\n3\nfalse true true\n2 c\n[{small}]\n\
         65540 5 1\n3 5\n2147450881\narray 65536 65536 true\n2147450885\n"
    );
    prints(&program("positions", source), &expected);
}

#[test]
fn a_frame_past_the_end_of_the_stack_overflows() {
    // generics.large-arrays, and program.exit-statuses: each call holds two copies of 512 KiB, far
    // more in all than any stack, and the run ends with status 134.
    let source = r#"use std.array

fn down(a: array.Array<i64, 65536>, n: i64) -> i64 {
  if n == 0 { a[0] } else {
    var b = a
    b[0] += 1
    down(b, n - 1)
  }
}

fn main() / io {
  let a: array.Array<i64, 65536> = array.fill(1)
  print("{down(a, 10)}")
  print("{down(a, 1_000_000)}")
}
"#;
    let file = program("overflow", source);
    for (how, out) in ["run", "build"].iter().zip(runs(&file)) {
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            "11\n",
            "{how}: {out:?}"
        );
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            stderr.starts_with("fatal: stack overflow"),
            "{how}: {stderr}"
        );
        assert_eq!(out.status.code(), Some(134), "{how}: {out:?}");
    }
}

#[test]
fn only_an_array_past_both_limits_runs_out_of_memory() {
    // generics.large-arrays, each element of a nested array counted: 65,536 elements of 65
    // words each are past the 2^22 words compiled code holds but within the elements every
    // array must hold, and 40,000 arrays of 2 are past those elements but within the words, so
    // both run; 40,000 arrays of 128 are past both, and the function that would hold them ends
    // the run as running out of memory does, after what came before it printed.
    let fields = |f: &dyn Fn(usize) -> String| (0..65).map(f).collect::<Vec<_>>().join(", ");
    let source = format!(
        "use std.array\n\ntype Wide = {{ {} }}\n\nfn wide() -> i64 {{\n  \
         let a: array.Array<Wide, 65536> = array.fill(Wide {{ {} }})\n  a[65535].w64 + a[0].w1\n}}\n\n\
         fn nested() -> i64 {{\n  \
         let a: array.Array<array.Array<i64, 2>, 40_000> = array.fill(array.fill(3))\n  \
         a[39_999][1]\n}}\n\n\
         fn deep() -> i64 {{\n  \
         let a: array.Array<array.Array<i64, 128>, 40_000> = array.fill(array.fill(1))\n  \
         a[0][0]\n}}\n\n\
         fn main() / io {{\n  print(\"{{wide()}} {{nested()}}\")\n  print(\"{{deep()}}\")\n}}\n",
        fields(&|i| format!("w{i}: i64")),
        fields(&|i| format!("w{i}: {i}")),
    );
    let file = program("limits", &source);
    for (how, out) in ["run", "build"].iter().zip(runs(&file)) {
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            "65 3\n",
            "{how}: {out:?}"
        );
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            stderr.starts_with("fatal: out of memory"),
            "{how}: {stderr}"
        );
        assert_eq!(out.status.code(), Some(134), "{how}: {out:?}");
    }
}
