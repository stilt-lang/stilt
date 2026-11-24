//! `check --edit` and `test --edit` (edits.command-line, edits.refusals and edits.edit-results):
//! what edits apply, the refusals with the file left as it was, the results, and the fixes of
//! diagnostics as edits. No conformance test observes them, so these are their tests.

mod common;

use std::fs;
use std::io::Write as _;
use std::path::Path;
use std::process::Stdio;
use std::time::Duration;

use common::{file, finish, hash, project, stderr, stdout, stilt};
use serde_json::Value;

fn text(path: &Path) -> String {
    fs::read_to_string(path).expect("the program is readable")
}

/// The current address, with its hash, of `address` in the program at `path`.
fn at(path: &Path, address: &str) -> String {
    let output = stilt(&["show", "--json", address, path.to_str().unwrap()], None);
    finish(path);
    let line = stdout(&output);
    let record: Value = serde_json::from_str(line.lines().next().expect("a record")).unwrap();
    record["at"].as_str().expect("an `at`").to_owned()
}

/// The canonical text `show` gives for `address`.
fn show_text(path: &Path, address: &str) -> String {
    let output = stilt(&["show", "--json", address, path.to_str().unwrap()], None);
    finish(path);
    let record: Value = serde_json::from_str(stdout(&output).lines().next().unwrap()).unwrap();
    record["text"].as_str().unwrap().to_owned()
}

/// Runs `stilt check --json` on the program with the edits, and parses what it writes.
fn check(path: &Path, edits: &[(&str, &str)]) -> (Option<i32>, Value) {
    let mut args = vec!["check", "--json"];
    for (at, new) in edits {
        args.extend(["--edit", at, new]);
    }
    args.push(path.to_str().unwrap());
    let output = stilt(&args, None);
    finish(path);
    let json = serde_json::from_slice(&output.stdout).unwrap_or(Value::Null);
    (output.status.code(), json)
}

const KINDS: &str = "/// A point.\ntype Point = { x: i64, y: i64 }\n\nconst ORIGIN: Point = Point { x: 0, y: 0 }\n\ntrait Shape {\n  fn area(self) -> i64\n  fn twice(self) -> i64 { self.area() * 2 }\n}\n\nimpl Point {\n  pub const LIMIT: i64 = 10\n  fn norm(self) -> i64 { self.x * self.x + self.y * self.y }\n}\n\nimpl Shape for Point {\n  fn area(self) -> i64 { 0 }\n}\n\ntest \"parses\" { assert(true) }\n\nfn main() { }\n";

#[test]
fn an_edit_of_each_kind_of_part_applies_and_reports_the_new_hash() {
    // edits.command-line, edits.new-text, edits.writing and edits.edit-results.
    let cases = [
        (
            "main.Point",
            "/// A 2D point.\ntype Point = { x: i64, y: i64 }",
        ),
        ("main.ORIGIN/body", "Point { x: 1, y: 1 }"),
        ("main.Shape.twice/body", "{ self.area() + self.area() }"),
        ("main.Point.LIMIT", "pub const LIMIT: i64 = 11"),
        ("main.Point.norm/body", "{ self.x * self.x }"),
        ("main.Point.Shape.area", "fn area(self) -> i64 { 1 }"),
        ("main.\"parses\"/body", "{ assert(1 == 1) }"),
        ("main.main", "fn main() { let n = 1 }"),
    ];
    for (n, (address, new)) in cases.iter().enumerate() {
        let path = file("edit-apply", &format!("kind{n}"), KINDS);
        let before = at(&path, address);
        let (status, json) = check(&path, &[(&before, new)]);
        assert_eq!(status, Some(0), "{address}: {json}");
        let result = &json["edits"][0];
        assert_eq!(result["applied"], true, "{address}");
        assert_eq!(result["at"], before.as_str());
        assert!(result.get("refused").is_none());
        // `now` is the part's address with the hash of its new canonical text.
        assert_eq!(result["now"], at(&path, address).as_str(), "{address}");
        // The text on disk reads as the new text, with the formatter's spacing.
        let shown = &show_text(&path, address);
        assert!(text(&path).contains(shown.as_str()), "{address}");
    }
}

#[test]
fn an_edit_reads_its_text_from_standard_input() {
    let path = file("edit-apply", "stdin", KINDS);
    let before = at(&path, "main.Point.norm/body");
    let output = stilt(
        &[
            "check",
            "--json",
            "--edit",
            &before,
            "-",
            path.to_str().unwrap(),
        ],
        Some("{ self.y }\n"),
    );
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    assert!(text(&path).contains("fn norm(self) -> i64 { self.y }"));
}

#[test]
fn an_edit_that_renames_a_declaration_moves_its_address() {
    let path = file("edit-apply", "rename", KINDS);
    let before = at(&path, "main.Point.norm");
    let (status, json) = check(&path, &[(&before, "fn length(self) -> i64 { self.x }")]);
    assert_eq!(status, Some(0));
    let now = json["edits"][0]["now"].as_str().unwrap();
    let canonical = "fn length(self) -> i64 { self.x }";
    assert_eq!(now, format!("main.Point.length#{}", hash(canonical)));
    assert_eq!(at(&path, "main.Point.length"), now);
}

#[test]
fn an_edit_is_written_as_the_formatter_writes_it_in_its_place() {
    // edits.writing: at the part's indentation, in the layout of its place, with every byte outside
    // the part as it was, in a file that isn't canonical.
    let source = "type P = {x:i64}\n\n\nimpl P {\n        fn  f(self)->i64{ 0 }  \n\n   // kept\n}\n\nfn main() { }\n";
    let path = file("edit-apply", "bytes", source);
    let before = at(&path, "main.P.f");
    let new = "fn f(self) -> i64 { let a = self.x + self.x + self.x + self.x + self.x + self.x + self.x + self.x + 1000; a }";
    let (status, _) = check(&path, &[(&before, new)]);
    assert_eq!(status, Some(0));
    let expected = "type P = {x:i64}\n\n\nimpl P {\n        fn f(self) -> i64 {\n          let a = self.x + self.x + self.x + self.x + self.x + self.x + self.x + self.x + 1000\n          a\n        }  \n\n   // kept\n}\n\nfn main() { }\n";
    assert_eq!(text(&path), expected);
}

/// The result of the one edit that `edits` refuses, with the file left byte for byte.
fn refused(name: &str, source: &str, address: &str, new: &str) -> Value {
    let path = file("edit-apply", name, source);
    let address = if address.contains('@') {
        address.replace('@', &at_of(&path, address))
    } else {
        address.to_owned()
    };
    let (status, json) = check(&path, &[(&address, new)]);
    assert_eq!(status, Some(2), "{name}: {json}");
    assert_eq!(text(&path), source, "{name} changed its file");
    assert!(json.get("diagnostics").is_none() && json.get("tests").is_none());
    assert_eq!(json["edits"].as_array().unwrap().len(), 1);
    json["edits"][0].clone()
}

/// The hash of the part at the path before `@` in an address, as `#hash`.
fn at_of(path: &Path, address: &str) -> String {
    let part = address.split('@').next().unwrap();
    format!("#{}", at(path, part).rsplit('#').next().unwrap())
}

const ONE: &str = "fn totals(orders: List<i64>) -> i64 { orders.len() }\n";

#[test]
fn each_refusal_gives_its_code_and_leaves_the_file_as_it_was() {
    // edits.refusals and edits.edit-results.
    let malformed = refused("e0700", ONE, "main.totals/body#45b", "{ 1 }");
    assert_eq!(malformed["refused"], "E0700");
    assert!(malformed.get("now").is_none(), "no part has the path");
    let none = refused("e0701", ONE, "main.total/body#45bc", "{ 1 }");
    assert_eq!(none["refused"], "E0701");
    assert!(none.get("now").is_none());
    let stale = refused("e0703", ONE, "main.totals/body#0000", "{ 1 }");
    assert_eq!(stale["refused"], "E0703");
    // `now` is the current address of the part.
    let body = "{ orders.len() }";
    assert_eq!(stale["now"], format!("main.totals/body#{}", hash(body)));
    let parse = refused("e0704", ONE, "main.totals/body@", "{ 1 ) }");
    assert_eq!(parse["refused"], "E0704");
    assert_eq!(parse["now"], format!("main.totals/body#{}", hash(body)));
    assert_eq!(parse["syntax"]["code"], "E0100");
    assert_eq!(parse["syntax"]["line"], 1);
    assert_eq!(parse["syntax"]["col"], 5);
    // A text that parses, as another kind of part.
    let other = refused("e0704b", ONE, "main.totals@", "type T = { a: i64 }");
    assert_eq!(other["refused"], "E0704");
    assert!(other.get("syntax").is_none());
    // A declaration has no body to replace with a declaration, and a body is no declaration.
    assert_eq!(
        refused("e0704c", ONE, "main.totals@", "{ 1 }")["refused"],
        "E0704"
    );
    assert_eq!(
        refused("e0704d", ONE, "main.totals/body@", "fn f() { }")["refused"],
        "E0704"
    );
}

#[test]
fn types_traits_the_standard_library_have_no_part_to_edit() {
    // edits.refusals, E0701: no body, and a part of `std`.
    let source = "type T = { a: i64 }\n\nfn main() { }\n";
    let path = file("edit-apply", "nobody", source);
    let (status, json) = check(&path, &[("main.T/body#aaaa", "{ 1 }")]);
    assert_eq!(status, Some(2));
    assert_eq!(json["edits"][0]["refused"], "E0701");
    let (status, json) = check(
        &path,
        &[("std.prelude.Option#1fa2", "type Option = | None")],
    );
    assert_eq!(status, Some(2));
    assert_eq!(json["edits"][0]["refused"], "E0701");
    assert_eq!(text(&path), source);
}

#[test]
fn a_path_that_names_two_parts_is_ambiguous_only_when_both_have_the_hash() {
    // edits.one-part-per-path and edits.refusals, E0702.
    let same = "fn twice() -> i64 { 1 }\n\nfn twice() -> i64 { 1 }\n";
    let path = file("edit-apply", "ambiguous", same);
    let current = at(&path, "main.twice");
    let (status, json) = check(&path, &[(&current, "fn twice() -> i64 { 2 }")]);
    assert_eq!(status, Some(2));
    assert_eq!(json["edits"][0]["refused"], "E0702");
    assert!(json["edits"][0].get("now").is_none());
    assert_eq!(text(&path), same);
    // With different texts, the hash picks one, and a rename fixes the duplicate.
    let different = "fn twice() -> i64 { 1 }\n\nfn twice() -> i64 { 2 }\n";
    let path = file("edit-apply", "tell-apart", different);
    let output = stilt(
        &["show", "--json", "main.twice", path.to_str().unwrap()],
        None,
    );
    let second: Value = serde_json::from_str(stdout(&output).lines().nth(1).unwrap()).unwrap();
    let (status, json) = check(
        &path,
        &[(second["at"].as_str().unwrap(), "fn thrice() -> i64 { 2 }")],
    );
    assert_eq!(status, Some(0), "{json}");
    assert_eq!(
        text(&path),
        "fn twice() -> i64 { 1 }\n\nfn thrice() -> i64 { 2 }\n"
    );
}

#[test]
fn overlapping_edits_are_refused_together() {
    // edits.refusals, E0705: both edit one part, or a declaration and its body.
    let path = file("edit-apply", "overlap", ONE);
    let decl = at(&path, "main.totals");
    let body = at(&path, "main.totals/body");
    let (status, json) = check(
        &path,
        &[
            (&decl, "fn totals(orders: List<i64>) -> i64 { 0 }"),
            (&body, "{ 1 }"),
        ],
    );
    assert_eq!(status, Some(2));
    let edits = json["edits"].as_array().unwrap();
    assert!(
        edits
            .iter()
            .all(|e| e["refused"] == "E0705" && e["applied"] == false)
    );
    let (status, json) = check(&path, &[(&body, "{ 1 }"), (&body, "{ 2 }")]);
    assert_eq!(status, Some(2));
    assert_eq!(json["edits"][1]["refused"], "E0705");
    assert_eq!(text(&path), ONE);
}

#[test]
fn a_second_edit_that_reads_standard_input_is_malformed() {
    let path = file("edit-apply", "twice-stdin", ONE);
    let body = at(&path, "main.totals/body");
    let decl = at(&path, "main.totals");
    let output = stilt(
        &[
            "check",
            "--json",
            "--edit",
            &body,
            "-",
            "--edit",
            &decl,
            "-",
            path.to_str().unwrap(),
        ],
        Some("{ 1 }"),
    );
    assert_eq!(output.status.code(), Some(2));
    let json: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(json["edits"][1]["refused"], "E0700");
    assert_eq!(text(&path), ONE);
}

#[test]
fn if_any_edit_is_refused_none_applies() {
    // edits.all-or-nothing.
    let source = "fn a() -> i64 { 1 }\n\nfn b() -> i64 { 2 }\n";
    let path = file("edit-apply", "all-or-none", source);
    let a = at(&path, "main.a/body");
    let (status, json) = check(&path, &[(&a, "{ 10 }"), ("main.b/body#0000", "{ 20 }")]);
    assert_eq!(status, Some(2));
    assert_eq!(json["edits"][0]["applied"], false);
    assert!(json["edits"][0].get("refused").is_none());
    assert_eq!(json["edits"][1]["refused"], "E0703");
    assert_eq!(text(&path), source);
    // Rendered for people, a refusal is a diagnostic on stderr and there is no verdict.
    let output = stilt(
        &[
            "check",
            "--edit",
            &a,
            "{ 10 }",
            "--edit",
            "main.b/body#0000",
            "{ 20 }",
            path.to_str().unwrap(),
        ],
        None,
    );
    assert_eq!(output.status.code(), Some(2));
    assert!(stderr(&output).contains("[E0703]"));
    assert_eq!(text(&path), source);
}

#[test]
fn edits_of_different_parts_of_one_file_all_apply_against_the_file_as_read() {
    // edits.all-or-nothing: the edits are checked before any applies, so a part's address holds
    // although an edit before it changed the file.
    let source = "fn a() -> i64 { 1 }\n\nfn b() -> i64 { 2 }\n";
    let path = file("edit-apply", "both", source);
    let a = at(&path, "main.a/body");
    let b = at(&path, "main.b");
    let (status, json) = check(
        &path,
        &[
            (&a, "{\n  let big = 1000000000\n  big\n}"),
            (&b, "fn b() -> i64 { 3 }"),
        ],
    );
    assert_eq!(status, Some(0), "{json}");
    assert!(
        json["edits"]
            .as_array()
            .unwrap()
            .iter()
            .all(|e| e["applied"] == true)
    );
    assert_eq!(
        text(&path),
        "fn a() -> i64 {\n  let big = 1000000000\n  big\n}\n\nfn b() -> i64 { 3 }\n"
    );
}

#[test]
fn of_two_commands_that_edit_one_part_from_one_hash_one_applies() {
    // edits.concurrent-edits.
    let path = file("edit-apply", "race", ONE);
    let body = at(&path, "main.totals/body");
    let spawn = |new: &str| {
        std::process::Command::new(env!("CARGO_BIN_EXE_stilt"))
            .args([
                "check",
                "--json",
                "--edit",
                &body,
                new,
                path.to_str().unwrap(),
            ])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("stilt runs")
    };
    let (one, two) = (spawn("{ 1 }"), spawn("{ 2 }"));
    let results: Vec<Value> = [one, two]
        .into_iter()
        .map(|c| {
            let output = c.wait_with_output().unwrap();
            serde_json::from_slice(&output.stdout).unwrap()
        })
        .collect();
    let applied = results
        .iter()
        .filter(|r| r["edits"][0]["applied"] == true)
        .count();
    assert_eq!(applied, 1, "{results:?}");
    let loser = results
        .iter()
        .find(|r| r["edits"][0]["applied"] == false)
        .unwrap();
    assert_eq!(loser["edits"][0]["refused"], "E0703");
}

#[test]
fn an_edit_read_while_another_command_writes_the_file_waits_for_the_write() {
    // edits.concurrent-edits: the writer holds the file's lock from its check to the end of its
    // write, here with the file emptied, so the edit must read it only once it is written.
    let path = file("edit-apply", "midway", ONE);
    let body = at(&path, "main.totals/body");
    let mut writer = fs::OpenOptions::new().write(true).open(&path).unwrap();
    writer.lock().unwrap();
    writer.set_len(0).unwrap();
    let edit = std::process::Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["check", "--json", "--edit", &body, "{ 1 }"])
        .arg(&path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("stilt runs");
    // Long enough for the edit to reach the lock.
    std::thread::sleep(Duration::from_millis(300));
    writer
        .write_all(b"fn totals(orders: List<i64>) -> i64 { 0 }\n")
        .unwrap();
    drop(writer);
    let output = edit.wait_with_output().unwrap();
    let result: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(result["edits"][0]["refused"], "E0703", "{result}");
}

#[test]
fn test_edit_runs_the_tests_of_the_edited_program() {
    let source =
        "fn double(x: i64) -> i64 { x + x + 1 }\n\ntest \"doubles\" { assert(double(2) == 4) }\n";
    let path = file("edit-apply", "test", source);
    let body = at(&path, "main.double/body");
    let output = stilt(&["test", "--json", path.to_str().unwrap()], None);
    assert_eq!(output.status.code(), Some(1));
    let output = stilt(
        &[
            "test",
            "--json",
            "--edit",
            &body,
            "{ x + x }",
            path.to_str().unwrap(),
        ],
        None,
    );
    let json: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(output.status.code(), Some(0), "{json}");
    assert_eq!(json["done"], true);
    assert_eq!(json["edits"][0]["applied"], true);
    // A refused edit gives no verdict.
    let output = stilt(
        &[
            "test",
            "--json",
            "--edit",
            "main.double/body#0000",
            "{ x }",
            path.to_str().unwrap(),
        ],
        None,
    );
    assert_eq!(output.status.code(), Some(2));
    let json: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert!(json.get("done").is_none() && json.get("tests").is_none());
    finish(&path);
}

#[test]
fn without_json_each_applied_edit_is_a_line_before_the_verdict() {
    let path = file("edit-apply", "lines", "fn f() -> i64 { cuont }\n");
    let body = at(&path, "main.f/body");
    let output = stilt(
        &["check", "--edit", &body, "{ 1 }", path.to_str().unwrap()],
        None,
    );
    assert_eq!(output.status.code(), Some(0));
    let now = hash("{ 1 }");
    assert_eq!(stderr(&output), format!("applied {body} -> #{now}\n"));
}

#[test]
fn a_directory_program_takes_edits_of_the_files_of_its_modules() {
    let orders = "pub fn qty() -> i64 { 1 }\n";
    let main = "use orders\n\nfn main() { }\n";
    let dir = project(
        "edit-apply",
        "modules",
        &[("orders.lt", orders), ("main.lt", main)],
    );
    let before = at(&dir, "orders.qty/body");
    let (status, json) = check(&dir, &[(&before, "{ 2 }")]);
    assert_eq!(status, Some(0), "{json}");
    assert_eq!(text(&dir.join("orders.lt")), "pub fn qty() -> i64 { 2 }\n");
    assert_eq!(text(&dir.join("main.lt")), main);
}
