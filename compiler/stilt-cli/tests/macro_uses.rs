//! How checking treats procedural macros and their uses: a spliced negative number, and a quote's
//! own `-` before a number, make a negative literal (macros.splices; numbers.negative-literals), a
//! macro's body is no duplicate of another's (docs.bodies-compared), and a failed use reports
//! nothing further (macros.failed-uses).

mod common;

use common::{finish, project, stdout, stilt};
use serde_json::Value;

const TOOLS: &str = "use std.meta

/// The least `i8`, and one less.
pub macro least() -> meta.Expr {
  let n = -128
  quote { $n }
}

pub macro below() -> meta.Expr {
  let n = -129
  quote { $n }
}

/// The least `i8` as the quote writes it, and a `-` apart from its digits, which negates.
pub macro written() -> meta.Expr { quote { -128 } }

pub macro apart() -> meta.Expr { quote { - 128 } }

/// Two macros of the same body, of more than 20 tokens.
pub macro first(e: meta.Expr) -> meta.Expr {
  let a = 1 + 2 + 3 + 4
  let b = a * 2 + a * 3
  quote { $e + $a + $b }
}

pub macro second(e: meta.Expr) -> meta.Expr {
  let a = 1 + 2 + 3 + 4
  let b = a * 2 + a * 3
  quote { $e + $a + $b }
}

/// Uses that always fail.
pub macro no_pattern(ts: meta.Tokens) -> meta.Pattern / raise<meta.Error> {
  raise meta.error(ts.close, \"no pattern\")
}

pub macro no_type(ts: meta.Tokens) -> meta.Type / raise<meta.Error> {
  raise meta.error(ts.close, \"no type\")
}
";

/// The code, line and message of each diagnostic of `stilt check --json` on a project of
/// `tools.lt` and `main.lt`.
fn diagnostics(name: &str, main: &str) -> Vec<(String, u64, String)> {
    let dir = project(
        "macro_uses",
        name,
        &[("tools.lt", TOOLS), ("main.lt", main)],
    );
    let output = stilt(&["check", "--json", dir.to_str().unwrap()], None);
    finish(&dir);
    let json: Value = serde_json::from_slice(&output.stdout).expect("JSON");
    json["diagnostics"]
        .as_array()
        .expect("diagnostics")
        .iter()
        .map(|d| {
            let code = d["code"].as_str().unwrap_or_default().to_owned();
            let message = d["message"].as_str().unwrap_or_default().to_owned();
            (code, d["line"].as_u64().unwrap_or(0), message)
        })
        .collect()
}

#[test]
fn a_spliced_negative_number_is_checked_as_a_negative_literal() {
    let main = "meta use tools\n\nfn main() / io {\n  let a: i8 = tools.least!()\n  \
                print(\"{a}\")\n}\n";
    assert_eq!(diagnostics("least", main), Vec::new());
    let dir = project(
        "macro_uses",
        "least_run",
        &[("tools.lt", TOOLS), ("main.lt", main)],
    );
    let output = stilt(&["run", dir.to_str().unwrap()], None);
    finish(&dir);
    assert_eq!(stdout(&output), "-128\n");
    let main = "meta use tools\n\nfn main() / io {\n  let a: i8 = tools.below!()\n  \
                print(\"{a}\")\n}\n";
    let found = diagnostics("below", main);
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].0, "E0320");
    assert_eq!(found[0].2, "-129 doesn't fit in `i8`");
}

#[test]
fn a_quotes_own_minus_before_a_number_is_part_of_it() {
    let main = "meta use tools\n\nfn main() / io {\n  let a: i8 = tools.written!()\n  \
                print(\"{a}\")\n}\n";
    assert_eq!(diagnostics("written", main), Vec::new());
    let main = "meta use tools\n\nfn main() / io {\n  let a: i8 = tools.apart!()\n  \
                print(\"{a}\")\n}\n";
    let found = diagnostics("apart", main);
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].0, "E0320");
}

#[test]
fn a_macros_body_is_no_duplicate() {
    // Two functions of the same body are W0302, and two macros of the same body aren't.
    let main = "meta use tools\n\nfn main() / io {\n  print(\"{tools.first!(1)} \
                {tools.second!(2)} {one([1])} {two([2])}\")\n}\n\nfn one(xs: List<i64>) -> \
                i64 {\n  var total = 0\n  for x in xs { total += x * 2 + 1 }\n  total + \
                xs.len() * 3\n}\n\nfn two(xs: List<i64>) -> i64 {\n  var total = 0\n  for x \
                in xs { total += x * 2 + 1 }\n  total + xs.len() * 3\n}\n";
    let found = diagnostics("duplicates", main);
    let codes: Vec<&str> = found.iter().map(|(code, _, _)| code.as_str()).collect();
    assert_eq!(codes, ["W0302"], "{found:?}");
    assert!(found[0].2.contains("`main.one`"), "{found:?}");
}

#[test]
fn a_failed_use_in_a_pattern_binds_nothing_and_its_scope_reports_no_unknown_name() {
    let main = "meta use tools\n\nfn main() / io {\n  let tools.no_pattern!(q) = 5\n  \
                print(\"{q} {r}\")\n  match 3 {\n    tools.no_pattern!(z) => print(\"{z}\")\n  \
                }\n}\n\nfn later() -> i64 { q }\n";
    let found = diagnostics("pattern", main);
    let codes: Vec<(&str, u64)> = found.iter().map(|(c, l, _)| (c.as_str(), *l)).collect();
    // A name outside the scopes the failed patterns open is reported as ever.
    assert_eq!(
        codes,
        [("E0225", 4), ("E0225", 7), ("E0211", 11)],
        "{found:?}"
    );
}

#[test]
fn a_literal_whose_expected_type_is_the_error_type_is_not_range_checked() {
    let main = "meta use tools\n\nfn main() / io {\n  let n: tools.no_type!(x) = 300\n  \
                let m: tools.no_type!(y) = 99999999999999999999999999\n  print(\"{n} {m}\")\n}\n";
    let found = diagnostics("literal", main);
    let codes: Vec<(&str, u64)> = found.iter().map(|(c, l, _)| (c.as_str(), *l)).collect();
    assert_eq!(codes, [("E0225", 4), ("E0225", 5)], "{found:?}");
}
