//! Profiles (builds.profiles):
//! `run --profile` and `test --profile` add their counts to the program's profile, each rounded
//! down to a power of two, in sorted lines; a run that ends with status 134 writes nothing; an
//! edit of a body drops its lines, which the performance report lists, and an edit above it
//! keeps them; a line not of the form is E0610; and a release build prints the same with a
//! profile as without one, the profile telling clang only which branches are likely, a `match`'s
//! tests among them.
//!
//! Each count below is derived from the program and the rule: a body's entry is counted at its
//! first line and the column of its `{`, an `if`'s first arm at its condition and its `else` at
//! the `else`'s block, a loop's body at the loop, and a call through a function value at the
//! call, with the address of the function it reaches.

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use common::hash;

/// The program: `parity` entered three times, twice for an even number, through `apply`'s call
/// of a function value, from a loop whose body runs three times.
const SOURCE: &str = "fn parity(n: i64) -> str {\n  if n % 2 == 0 { \"even\" } else { \"odd\" }\n}\n\n\
                      fn apply(f: fn(i64) -> str, n: i64) -> str { f(n) }\n\n\
                      fn main() / io {\n  for i in 0..3 {\n    print(apply(parity, i))\n  }\n}\n";

/// The canonical text of each body, which `stilt fmt` writes on one line (edits.canonical-text),
/// whose hash the profile's lines hold.
const PARITY: &str = "{ if n % 2 == 0 { \"even\" } else { \"odd\" } }";
const APPLY: &str = "{ f(n) }";
const MAIN: &str = "{ for i in 0..3 { print(apply(parity, i)) } }";

fn source() -> String {
    SOURCE.to_owned()
}

/// The profile after `runs` runs of the program, whose counts are, for one run: `apply`
/// entered 3 times and its call reaching `parity` 3 times, `main` entered once and its loop's
/// body run 3 times, and `parity` entered 3 times, its first arm taken twice and its `else`
/// once.
fn profile(counts: [u64; 7]) -> String {
    let (apply, main, parity) = (hash(APPLY), hash(MAIN), hash(PARITY));
    format!(
        "main.apply/body {apply} entry 1:44 {}\n\
         main.apply/body {apply} call 1:46 main.parity {}\n\
         main.main/body {main} entry 1:16 {}\n\
         main.main/body {main} loop 2:3 {}\n\
         main.parity/body {parity} entry 1:26 {}\n\
         main.parity/body {parity} arm 2:6 {}\n\
         main.parity/body {parity} arm 2:33 {}\n",
        counts[0], counts[1], counts[2], counts[3], counts[4], counts[5], counts[6]
    )
}

fn stilt(args: &[&str], path: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(args)
        .arg(path)
        .env("STILT_HOME", path.with_file_name("home"))
        .env_remove("STILT_CC")
        .output()
        .expect("stilt runs")
}

fn written(path: &Path) -> String {
    fs::read_to_string(path.with_extension("profile")).unwrap_or_default()
}

fn program(name: &str) -> PathBuf {
    common::file("profiles", name, &source())
}

#[test]
fn profiled_runs_add_their_counts_and_round_the_sum_down() {
    let path = program("twice");
    let ran = stilt(&["run", "--profile"], &path);
    assert!(ran.status.success(), "{ran:?}");
    assert_eq!(common::stdout(&ran), "even\nodd\neven\n");
    assert_eq!(written(&path), profile([2, 2, 1, 2, 2, 2, 1]));
    assert!(stilt(&["run", "--profile"], &path).status.success());
    // 2 + 3 is 5, which rounds down to 4; 1 + 1 is 2; 2 + 2 is 4.
    assert_eq!(written(&path), profile([4, 4, 2, 4, 4, 4, 2]));
}

#[test]
fn the_same_runs_write_the_same_sorted_file() {
    let (a, b) = (program("same_a"), program("same_b"));
    for path in [&a, &b] {
        assert!(stilt(&["run", "--profile"], path).status.success());
    }
    let text = written(&a);
    assert_eq!(text, written(&b));
    let mut lines: Vec<&str> = text.lines().collect();
    let shown = lines.clone();
    lines.sort_by_key(|l| {
        let words: Vec<&str> = l.split(' ').collect();
        let (line, col) = words[3].split_once(':').expect("a place");
        let place: (u32, u32) = (
            line.parse().expect("a line"),
            col.parse().expect("a column"),
        );
        (words[0].to_owned(), words[1].to_owned(), place)
    });
    assert_eq!(lines, shown);
}

#[test]
fn a_profiled_test_run_counts_the_tests() {
    let source = format!(
        "{}\ntest \"four is even\" {{\n  assert parity(4) == \"even\"\n}}\n",
        source()
    );
    let path = common::file("profiles", "tests", &source);
    let tested = stilt(&["test", "--profile"], &path);
    assert!(tested.status.success(), "{tested:?}");
    let text = written(&path);
    let parity = hash(PARITY);
    for line in [
        format!("main.parity/body {parity} entry 1:26 1"),
        format!("main.parity/body {parity} arm 2:6 1"),
    ] {
        assert!(text.lines().any(|l| l == line), "{line} in\n{text}");
    }
    assert!(!text.contains("arm 2:33"), "{text}");
}

#[test]
fn only_a_run_that_ends_with_status_134_writes_nothing() {
    let deep = "fn down(n: i64) -> i64 {\n  if n == 0 { 0 } else { 1 + down(n + 1) }\n}\n\n\
                fn main() / io { print(\"{down(1)}\") }\n";
    let path = common::file("profiles", "overflow", deep);
    let ran = stilt(&["run", "--profile"], &path);
    assert_eq!(ran.status.code(), Some(134), "{ran:?}");
    assert!(!path.with_extension("profile").exists());
    let panics =
        "fn main() / io {\n  let xs = [1]\n  for i in 0..2 {\n    print(\"{xs[i]}\")\n  }\n}\n";
    let path = common::file("profiles", "panic", panics);
    let ran = stilt(&["run", "--profile"], &path);
    assert_eq!(ran.status.code(), Some(101), "{ran:?}");
    let main = hash("{\n  let xs = [1]\n  for i in 0..2 { print(\"{xs[i]}\") }\n}");
    let expected =
        format!("main.main/body {main} entry 1:16 1\nmain.main/body {main} loop 3:3 2\n");
    assert_eq!(written(&path), expected);
}

#[test]
fn an_edited_body_drops_its_lines_and_an_edit_above_keeps_them() {
    let path = program("edited");
    assert!(stilt(&["run", "--profile"], &path).status.success());
    let before = written(&path);
    let changed = source().replace("\"odd\" }", "\"not even\" }");
    fs::write(&path, &changed).expect("the program can be written");
    let report = stilt(&["show", "--release", "main.parity"], &path);
    let text = common::stdout(&report);
    let stale: Vec<&str> = before
        .lines()
        .filter(|l| l.starts_with("main.parity/"))
        .collect();
    let listed: Vec<&str> = (text.lines())
        .skip_while(|l| !l.starts_with("  profile:"))
        .skip(1)
        .map(str::trim)
        .collect();
    assert!(text.contains("  profile: 3 lines dropped"), "{text}");
    assert_eq!(listed, stale);
    let apply = common::stdout(&stilt(&["show", "--release", "main.apply"], &path));
    assert!(!apply.contains("profile:"), "{apply}");
    fs::write(&path, format!("// Even or odd.\n\n{}", source())).expect("writable");
    let moved = common::stdout(&stilt(&["show", "--release", "main.parity"], &path));
    assert!(!moved.contains("profile:"), "{moved}");
    assert!(stilt(&["run", "--profile"], &path).status.success());
    assert_eq!(written(&path), profile([4, 4, 2, 4, 4, 4, 2]));
}

#[test]
fn a_malformed_line_is_an_error_naming_it() {
    let path = program("malformed");
    let parity = hash(PARITY);
    let bad =
        format!("main.parity/body {parity} entry 1:26 2\nmain.parity/body {parity} arm 2:6 3\n");
    fs::write(path.with_extension("profile"), &bad).expect("the profile can be written");
    let checked = stilt(&["check", "--json"], &path);
    assert_eq!(checked.status.code(), Some(1), "{checked:?}");
    let json: serde_json::Value = serde_json::from_slice(&checked.stdout).expect("JSON");
    let d = &json["diagnostics"][0];
    assert_eq!(
        (&d["code"], &d["file"], &d["line"]),
        (&"E0610".into(), &"main.profile".into(), &2.into())
    );
    for args in [&["build", "--release"][..], &["run", "--profile"]] {
        let refused = stilt(args, &path);
        assert_eq!(refused.status.code(), Some(2), "{args:?}: {refused:?}");
        let stderr = common::stderr(&refused);
        assert!(
            stderr.contains("[E0610]") && stderr.contains("main.profile:2:1"),
            "{stderr}"
        );
    }
    assert_eq!(written(&path), bad);
}

#[test]
fn a_release_build_prints_the_same_with_a_profile_and_without_one() {
    let path = program("release");
    let dir = path.parent().expect("a directory").to_path_buf();
    let built = |name: &str| {
        let c = dir.join(format!("{name}.c"));
        let exe = dir.join(name);
        let out = Command::new(env!("CARGO_BIN_EXE_stilt"))
            .args(["build", "--release", "-o"])
            .arg(&exe)
            .arg(&path)
            .env("STILT_HOME", dir.join("home"))
            .env("STILT_C_DIR", &c)
            .env_remove("STILT_CC")
            .output()
            .expect("stilt runs");
        assert!(out.status.success(), "{out:?}");
        let ran = Command::new(&exe).output().expect("the program runs");
        let hinted = fs::read_dir(&c).expect("the C is kept").flatten().any(|f| {
            fs::read_to_string(f.path())
                .is_ok_and(|t| t.contains("__builtin_expect_with_probability"))
        });
        (ran.status.code(), ran.stdout, hinted)
    };
    let without = built("without");
    assert!(stilt(&["run", "--profile"], &path).status.success());
    let with = built("with");
    assert_eq!((&with.0, &with.1), (&without.0, &without.1));
    assert_eq!((without.2, with.2), (false, true));
}

/// A `match` of three variants that a profiled run takes once, twice and once: its first test is
/// told it holds 1 time in 4, the arms after it taking the other 3, and its second 2 times in 3
/// (builds.profile-use).
#[test]
fn a_match_s_tests_are_told_how_often_their_arms_are_taken() {
    let source = "type Shape = | Dot | Square(i64) | Line(i64)\n\n\
                  fn size(s: Shape) -> i64 {\n  match s {\n    Dot => 0\n    Square(n) => n * n\n    Line(n) => n\n  }\n}\n\n\
                  fn main() / io {\n  for s in [Dot, Square(2), Square(3), Line(4)] {\n    print(\"{size(s)}\")\n  }\n}\n";
    let path = common::file("profiles", "match", source);
    let dir = path.parent().expect("a directory").to_path_buf();
    assert!(stilt(&["run", "--profile"], &path).status.success());
    let arms: Vec<String> = (written(&path).lines())
        .filter(|l| l.starts_with("main.size/") && l.contains(" arm "))
        .map(|l| l.rsplit(' ').next().unwrap_or_default().to_owned())
        .collect();
    assert_eq!(arms, ["1", "2", "1"]);
    let c = dir.join("match.c");
    let out = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["build", "--release", "-o"])
        .arg(dir.join("match"))
        .arg(&path)
        .env("STILT_HOME", dir.join("home"))
        .env("STILT_C_DIR", &c)
        .env_remove("STILT_CC")
        .output()
        .expect("stilt runs");
    assert!(out.status.success(), "{out:?}");
    let text: String = (fs::read_dir(&c).expect("the C is kept").flatten())
        .filter_map(|f| fs::read_to_string(f.path()).ok())
        .collect();
    for p in ["0.2500", "0.6667"] {
        assert!(text.contains(&format!(" != 0, 1, {p})")), "no hint of {p}");
    }
}
