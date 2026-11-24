//! Value parameters, arrays and staging annotations (generics.value-parameters and generics.arrays;
//! meta.staging-annotations), run in memory by `stilt run` and as executables that `stilt build`
//! writes: each program prints what the Reference gives it, and ends with every count back to zero,
//! which a debug build's check at exit would fail otherwise (goal no-leaks).

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};

/// Writes `source` as a program of its own directory, and gives its file.
fn program(name: &str, source: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("arrays")
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    let file = dir.join("main.lt");
    fs::write(&file, source).expect("the program can be written");
    file
}

/// The program's run with `stilt run`, then the run of the executable `stilt build` writes.
fn runs(name: &str, source: &str) -> [Output; 2] {
    let file = program(name, source);
    let stilt = env!("CARGO_BIN_EXE_stilt");
    let ran = Command::new(stilt)
        .arg("run")
        .arg(&file)
        .output()
        .expect("stilt runs");
    let exe = file.with_file_name("program");
    let built = Command::new(stilt)
        .args(["build", "-o"])
        .arg(&exe)
        .arg(&file)
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    let executed = Command::new(&exe).output().expect("the program runs");
    [ran, executed]
}

/// Checks that both runs of `source` print `expected` and succeed.
fn prints(name: &str, source: &str, expected: &str) {
    for (how, out) in ["run", "build"].iter().zip(runs(name, source)) {
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            expected,
            "{how}: {out:?}"
        );
        assert!(out.status.success(), "{how}: {out:?}");
    }
}

/// Checks that both runs of `source` print `expected`, then panic with `bounds` (std.lists), which
/// ends the program with status 101 (program.panic-report).
fn panics_with_bounds(name: &str, source: &str, expected: &str) {
    for (how, out) in ["run", "build"].iter().zip(runs(name, source)) {
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            expected,
            "{how}: {out:?}"
        );
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(stderr.starts_with("panic: bounds: "), "{how}: {stderr}");
        assert_eq!(out.status.code(), Some(101), "{how}: {out:?}");
    }
}

#[test]
fn the_record_s_example_prints_what_it_says() {
    // generics.arrays, Context.
    let source = r#"use std.array

type Mod<p: u64> = { value: u64 }

fn add<p: u64>(a: Mod<p>, b: Mod<p>) -> Mod<p> { Mod { value: (a.value + b.value) % p } }

fn dot<n: i64>(a: array.Array<i64, n>, b: array.Array<i64, n>) -> i64 {
  var sum = 0
  for i in 0..n { sum = sum + a[i] * b[i] }
  sum
}

const PRIME: u64 = 1_000_000_007

fn main() / io {
  let a: Mod<PRIME> = Mod { value: 5 }
  let b: Mod<1_000_000_007> = Mod { value: PRIME - 1 }
  print("{add(a, b).value}")
  let v: array.Array<i64, 3> = [1, 2, 3]
  let [x, _, z] = v
  print("{dot(v, v)} {x + z} {v}")
}
"#;
    prints("example", source, "4\n14 4 [1, 2, 3]\n");
}

#[test]
fn arrays_are_values_held_inline() {
    // generics.arrays, generics.array-patterns and generics.large-arrays on
    // 65,536 elements.
    let source = r#"use std.array

type Grid<k: i64> = { cells: array.Array<i64, k> }

fn bump(inout a: array.Array<i64, 3>) { a[1] += 10 }

fn incr(inout x: i64) { x += 1 }

fn first<T, n: i64>(a: array.Array<T, n>) -> T { a[0] }

fn total<n: i64>(a: array.Array<i64, n>) -> i64 {
  var s = 0
  for x in a { s += x }
  s
}

fn main() / io {
  let a: array.Array<i64, 3> = array.fill(7)
  print("{a} {a.len()} {a.to_list()} {a.map(|x| x * 10)}")
  let b: Option<array.Array<i64, 2>> = array.from_list([1, 2])
  let c: Option<array.Array<i64, 2>> = array.from_list([1])
  print("{b} {c}")
  var v: array.Array<i64, 3> = [1, 2, 3]
  let w = v
  v[0] = 100
  bump(inout v)
  incr(inout v[2])
  print("{v} {w}")
  let [x, ..] = v
  let [p, q, r] = v
  match v {
    [0, ..] => print("zero")
    [_, ..] => print("{x} {p} {q} {r}")
  }
  let s: array.Array<str, 2> = ["a", "b"]
  print("{s} {first(s)} {total(v)}")
  let g: Grid<2> = Grid { cells: [4, 5] }
  let nested: array.Array<array.Array<i64, 2>, 2> = [[1, 2], [3, 4]]
  print("{g} {nested} {nested[1][0]}")
  let l: array.Array<i64, 2> = [1, 2]
  let m: array.Array<i64, 2> = [1, 3]
  var keyed: Map<array.Array<i64, 2>, str> = Map.new()
  keyed[l] = "one"
  keyed[m] = "two"
  print("{l < m} {l == m} {l == [1, 2]} {keyed[[1, 3]]} {keyed.len()}")
  let e: array.Array<i64, 0> = []
  let big: array.Array<i64, 65536> = array.fill(1)
  print("{e} {total(e)} {total(big)}")
  match big {
    [0, ..] => print("zero")
    [x, _, ..] => print("{x}")
  }
}
"#;
    let expected = "[7, 7, 7] 3 [7, 7, 7] [70, 70, 70]\nSome([1, 2]) None\n\
        [100, 12, 4] [1, 2, 3]\n100 100 12 4\n[\"a\", \"b\"] a 116\n\
        Grid { cells: [4, 5] } [[1, 2], [3, 4]] 3\ntrue false true two 2\n[] 0 65536\n1\n";
    prints("arrays", source, expected);
}

#[test]
fn an_index_past_the_end_panics() {
    // generics.array-elements.
    let source = r#"use std.array

fn main() / io {
  var v: array.Array<i64, 3> = [1, 2, 3]
  for i in 0..4 { print("{v[i]}") }
}
"#;
    panics_with_bounds("past_the_end", source, "1\n2\n3\n");
}

#[test]
fn a_negative_size_has_no_values() {
    // generics.array-sizes: `from_list` gives `None`, and `fill` panics.
    let source = r#"use std.array

type Grid<k: i64> = { cells: array.Array<i64, k> }

fn listed<k: i64>(g: Option<Grid<k>>, xs: List<i64>) -> bool {
  let c: Option<array.Array<i64, k>> = array.from_list(xs)
  c.is_none()
}

fn make<k: i64>() -> Grid<k> { Grid { cells: array.fill(0) } }

fn main() / io {
  let none: Option<Grid<-1>> = None
  print("{listed(none, [])}")
  let g: Grid<-1> = make()
  print("{g}")
}
"#;
    panics_with_bounds("negative", source, "true\n");
}

/// A program that reads value parameters and writes staging annotations.
const STAGED: &str = r#"use std.array

type Mod<p: u64> = { value: u64 }

impl<p: u64> Mod<p> {
  fn new(v: u64) -> Mod<p> { Mod { value: v % p } }
  fn modulus(self) -> u64 { p }
}

impl<p: u64> Show for Mod<p> {
  fn show(self) -> str { "{self.value} mod {p}" }
}

type Flag<b: bool> = { x: i64 }

fn flag<b: bool>(f: Flag<b>) -> bool { b }

type Small<k: u8> = { v: i64 }

fn small<k: u8>(m: Small<k>) -> u8 { k }

fn add<p: u64>(a: Mod<p>, b: Mod<p>) -> Mod<p> { Mod { value: (a.value + b.value) % p } }

const PRIME: u64 = 1_000_000_007

const SIZE: i64 = 4

fn sum<n: i64>(a: array.Array<i64, n>) -> i64 {
  var t = 0
  comptime for i in 0..n { t += a[i] }
  t
}

fn pick<n: i64>(a: array.Array<i64, n>) -> str {
  comptime if n > 2 { "big" } else { "small" }
}

fn main() / io {
  let a: Mod<7> = Mod.new(10)
  let f: fn(Mod<7>, Mod<7>) -> Mod<7> = add
  let g = |x: Mod<PRIME>| add(x, x)
  print("{a} {a.modulus()} {f(a, a)} {g(Mod { value: 5 })}")
  let fl: Flag<true> = Flag { x: 1 }
  let sm: Small<255> = Small { v: 1 }
  print("{flag(fl)} {small(sm)}")
  let v: array.Array<i64, SIZE> = [1, 2, 3, 4]
  let w: array.Array<i64, 2> = [5, 6]
  print("{sum(v)} {pick(v)} {sum(w)} {pick(w)}")
  comptime match SIZE {
    4 => print("four")
    _ => print("other")
  }
}
"#;

#[test]
fn value_parameters_are_read_and_staging_erases() {
    // generics.value-parameters-in-body, and meta.erasure: the program and its copy without its
    // annotations print the same (goal staging-erases).
    let expected = "3 mod 7 7 6 mod 7 10 mod 1000000007\ntrue 255\n10 big 11 small\nfour\n";
    prints("staged", STAGED, expected);
    prints("erased", &STAGED.replace("comptime ", ""), expected);
}
