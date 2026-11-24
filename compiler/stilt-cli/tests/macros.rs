//! Macros as the commands show them: `show` prints a use as written, and with `--expanded` its
//! expansion in its place, each fresh name with its number (macros.showing), numbered in a
//! procedural macro's expansion as their bindings appear, and the lines each use's expansion
//! takes (macros.showing); an error in a template's own tokens is reported at the use, with a note
//! that shows the template (macros.errors-in-expansions); and the files a use names, read again
//! after an edit and refused through a link that leaves the package (macros.named-files). The
//! conformance suite checks what macros mean.

mod common;

use common::{file, finish, project, stdout, stilt};
use serde_json::Value;

const SWAP: &str = "syntax swap {\n  ($a: name, $b: name) => { let tmp = $a; $a = $b; $b = tmp }\n}

syntax unless {
  ($cond: expr) $body: block => if !($cond) $body
}

fn main() / io {
  var tmp = 1
  var y = 2
  swap!(tmp, y)
  unless!(tmp > y) {
    swap!(y, tmp)
  }
  print(\"{tmp} {y}\")
}
";

#[test]
fn show_prints_uses_as_written() {
    let path = file("macros", "written", SWAP);
    let output = stilt(&["show", "main.main", path.to_str().unwrap()], None);
    finish(&path);
    let text = stdout(&output);
    assert!(text.contains("  swap!(tmp, y)\n"), "{text}");
    assert!(
        text.contains("  unless!(tmp > y) {\n    swap!(y, tmp)\n  }\n"),
        "{text}"
    );
    assert!(!text.contains("tmp#"), "{text}");
}

#[test]
fn show_expanded_prints_each_expansion_with_its_fresh_names() {
    let path = file("macros", "expanded", SWAP);
    let output = stilt(
        &["show", "--expanded", "main.main", path.to_str().unwrap()],
        None,
    );
    finish(&path);
    let text = stdout(&output);
    // Each use's line reports the lines its expansion takes in the canonical format
    // (macros.showing; visible-expansion-size).
    assert!(
        text.contains("  { let tmp#1 = tmp; tmp = y; y = tmp#1 } // `swap!` expands to 5 lines\n"),
        "{text}"
    );
    // A use in a fragment is expanded in its place, with a number of its own, and an expansion
    // is written on one line.
    assert!(
        text.contains(
            "  if !((tmp > y)) { { let tmp#3 = y; y = tmp; tmp = tmp#3 } } // `unless!` expands \
             to 7 lines\n"
        ),
        "{text}"
    );
}

const NAMES: &str = "use std.meta

/// The value and the value plus one, each bound to a fresh name, made in the other order.
pub macro two(e: meta.Expr) -> meta.Expr {
  let b = meta.fresh(\"b\")
  let a = meta.fresh(\"a\")
  quote {
    let $a = $e
    let $b = $a + 1
    $a * $b
  }
}
";

#[test]
fn show_expanded_numbers_a_procedural_macros_fresh_names_as_their_bindings_appear() {
    let main = "meta use names\n\nfn main() / io {\n  let x = 3\n  print(\"{names.two!(x)}\")\n}\n";
    let dir = project(
        "macros",
        "procedural",
        &[("main.lt", main), ("names.lt", NAMES)],
    );
    let output = stilt(
        &["show", "--expanded", "main.main", dir.to_str().unwrap()],
        None,
    );
    finish(&dir);
    let text = stdout(&output);
    // `a` is made second but bound first, so it is `a#1` (macros.showing).
    assert!(
        text.contains("let a#1 = (x); let b#2 = a#1 + 1; a#1 * b#2"),
        "{text}"
    );
    assert!(text.contains("`names.two!` expands to 5 lines\n"), "{text}");
}

#[test]
fn an_error_in_a_template_is_at_the_use_with_a_note() {
    let source = "syntax size {\n  ($x: expr) => $x.len()\n}\n\nfn main() / io {\n  \
                  print(\"{size!(5)}\")\n}\n";
    let path = file("macros", "noted", source);
    let output = stilt(&["check", "--json", path.to_str().unwrap()], None);
    finish(&path);
    let json: Value = serde_json::from_slice(&output.stdout).expect("JSON");
    let d = &json["diagnostics"][0];
    assert_eq!(d["code"], "E0314");
    assert_eq!((d["line"].as_u64(), d["col"].as_u64()), (Some(6), Some(11)));
    let note = &d["labels"][1];
    assert_eq!(note["text"], "`size!` expands to this");
    assert_eq!(note["range"][0][0], 2);
}

const LINES: &str = "use std.meta

/// The number of lines of the file.
pub macro count(f: meta.File) -> meta.Expr {
  let n = f.text.value().lines().len()
  quote { $n }
}
";

#[test]
fn an_edit_of_a_named_file_expands_the_uses_that_name_it_again() {
    // A file a use names is an input of the program, which the engine reads again
    // (macros.named-files; sandboxed-compile-time-code).
    let main = "meta use lines\n\nfn main() / io {\n  let n = lines.count!(\"words.txt\")\n  print(\"{n}\")\n}\n";
    let files = [
        ("main.lt", main),
        ("lines.lt", LINES),
        ("words.txt", "a\nb\n"),
    ];
    let dir = project("macros", "named_file", &files);
    let first = stilt(&["run", dir.to_str().unwrap()], None);
    std::fs::write(dir.join("words.txt"), "a\nb\nc\n").expect("the file can be written");
    let second = stilt(&["run", dir.to_str().unwrap()], None);
    finish(&dir);
    assert_eq!(stdout(&first), "2\n");
    assert_eq!(stdout(&second), "3\n");
}

#[test]
fn a_named_file_that_links_outside_the_package_is_refused() {
    // A macro reads only files inside its user's package, whatever a link inside it points
    // to (macros.named-files): the real path of what a link names must lie in the directory.
    let main = "meta use lines\n\nfn inside() -> i64 { lines.count!(\"near.txt\") }\n\nfn outside() -> i64 { lines.count!(\"far.txt\") }\n\nfn main() {}\n";
    let files = [
        ("main.lt", main),
        ("lines.lt", LINES),
        ("words.txt", "a\nb\n"),
    ];
    let dir = project("macros", "linked_file", &files);
    let secret = common::directory("macros", "linked_secret").join("secret.txt");
    std::fs::write(&secret, "one\ntwo\nthree\n").expect("the file can be written");
    std::os::unix::fs::symlink(dir.join("words.txt"), dir.join("near.txt"))
        .expect("the link can be made");
    std::os::unix::fs::symlink(&secret, dir.join("far.txt")).expect("the link can be made");
    let checked = stilt(&["check", "--json", dir.to_str().unwrap()], None);
    finish(&dir);
    let report: Value = serde_json::from_slice(&checked.stdout).expect("the report is JSON");
    let codes: Vec<(&str, u64)> = report["diagnostics"]
        .as_array()
        .expect("a list of diagnostics")
        .iter()
        .map(|d| {
            (
                d["code"].as_str().unwrap_or(""),
                d["line"].as_u64().unwrap_or(0),
            )
        })
        .collect();
    assert_eq!(codes, [("E0229", 5)], "{}", stdout(&checked));
}
