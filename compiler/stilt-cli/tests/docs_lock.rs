//! Pinned docs (docs.pins, docs.lock-file and docs.stale): the pins that `stilt fmt` and `check
//! --edit` write into a package's `docs.lock`, and the stale docs that `check` reports as W0002.
//! Conformance can't observe them, since no conformance test holds a `docs.lock`
//! (docs.warnings-in-conformance).

mod common;

use std::fs;
use std::path::{Path, PathBuf};

use common::{directory, finish, hash, stilt};
use serde_json::Value;

const DOC: &str = "/// The weight of an order.";

/// No diagnostic.
const NONE: [&str; 0] = [];

/// A package named `orders` whose module `main` holds `source`.
fn package(name: &str, source: &str) -> PathBuf {
    let dir = directory("docs-lock", name);
    fs::create_dir_all(dir.join("src")).unwrap();
    fs::write(dir.join("stilt.toml"), "[package]\nname = \"orders\"\n").unwrap();
    fs::write(dir.join("src/main.lt"), source).unwrap();
    dir
}

fn weight(signature: &str, doc: &str) -> String {
    format!("{doc}\n{signature} {{ o * 2 }}\n\nfn main() / io {{ print(\"done\") }}\n")
}

fn lock(dir: &Path) -> Option<String> {
    fs::read_to_string(dir.join("docs.lock")).ok()
}

/// The pin of `main.weight` with the hashes of its signature's text and its doc's
/// (docs.pinned-texts).
fn pin(signature: &str, doc: &str) -> String {
    format!(
        "main.weight #{} #{}\n",
        hash(&format!("{signature} {{}}")),
        hash(doc)
    )
}

fn run(args: &[&str], dir: &Path) -> Value {
    let mut all = args.to_vec();
    all.push(dir.to_str().unwrap());
    let output = stilt(&all, None);
    finish(dir);
    serde_json::from_slice(&output.stdout).unwrap_or(Value::Null)
}

fn codes(json: &Value) -> Vec<String> {
    json["diagnostics"]
        .as_array()
        .map_or(&[][..], Vec::as_slice)
        .iter()
        .map(|d| d["code"].as_str().unwrap_or_default().to_owned())
        .collect()
}

#[test]
fn fmt_pins_new_docs_and_changed_ones() {
    let old = "fn weight(o: i64) -> i64";
    let dir = package("new", &weight(old, DOC));
    run(&["fmt"], &dir);
    assert_eq!(lock(&dir).unwrap(), pin(old, DOC));
    // A doc whose text changed is pinned again, with its new signature.
    let new = "fn weight(o: i64, unit: i64) -> i64";
    let doc = "/// The weight of an order, in units.";
    fs::write(dir.join("src/main.lt"), weight(new, doc)).unwrap();
    assert_eq!(codes(&run(&["check", "--json"], &dir)), NONE);
    run(&["fmt"], &dir.join("src/main.lt"));
    assert_eq!(lock(&dir).unwrap(), pin(new, doc));
}

#[test]
fn a_changed_signature_under_an_untouched_doc_is_stale() {
    let old = "fn weight(o: i64) -> i64";
    let dir = package("stale", &weight(old, DOC));
    run(&["fmt"], &dir);
    let new = "fn weight(o: i64, unit: i64) -> i64";
    fs::write(dir.join("src/main.lt"), weight(new, DOC)).unwrap();
    let json = run(&["check", "--json"], &dir);
    assert_eq!(codes(&json), ["W0002"]);
    assert_eq!(json["diagnostics"][0]["line"], 1);
    // `check` never writes `docs.lock`, and `fmt` keeps a stale pin.
    assert_eq!(lock(&dir).unwrap(), pin(old, DOC));
    run(&["fmt"], &dir);
    assert_eq!(lock(&dir).unwrap(), pin(old, DOC));
    // The fix sends the declaration back as it is, which pins its doc again (docs.writing-pins).
    let edit = &json["diagnostics"][0]["fixes"][0]["edits"][0];
    assert_eq!(edit["new"], format!("{DOC}\n{new} {{ o * 2 }}"));
    let at = edit["at"].as_str().unwrap();
    let text = edit["new"].as_str().unwrap();
    let fixed = run(&["check", "--json", "--edit", at, text], &dir);
    assert!(codes(&fixed).is_empty(), "{fixed}");
    assert_eq!(lock(&dir).unwrap(), pin(new, DOC));
}

#[test]
fn an_edit_of_a_signature_alone_leaves_its_doc_stale() {
    let old = "fn weight(o: i64) -> i64";
    let dir = package("edited", &weight(old, DOC));
    run(&["fmt"], &dir);
    let at = format!("main.weight#{}", hash(&format!("{DOC}\n{old} {{ o * 2 }}")));
    let new = format!("{DOC}\nfn weight(o: i64, unit: i64) -> i64 {{ o * unit }}");
    let json = run(&["check", "--json", "--edit", &at, &new], &dir);
    assert_eq!(codes(&json), ["W0002"]);
    // A body's edit changes no signature, so nothing is stale after it.
    let dir = package("body", &weight(old, DOC));
    run(&["fmt"], &dir);
    let body = format!("main.weight/body#{}", hash("{ o * 2 }"));
    let json = run(&["check", "--json", "--edit", &body, "{ o * 3 }"], &dir);
    assert_eq!(json["edits"][0]["applied"], true);
    assert_eq!(codes(&json), NONE);
    assert_eq!(lock(&dir).unwrap(), pin(old, DOC));
}

#[test]
fn a_doc_without_a_pin_is_never_stale_and_is_pinned_by_the_next_edit() {
    let old = "fn weight(o: i64) -> i64";
    let dir = package("unpinned", &weight(old, DOC));
    assert_eq!(codes(&run(&["check", "--json"], &dir)), NONE);
    assert_eq!(lock(&dir), None);
    // A refused edit writes no file, so no `docs.lock` either.
    run(
        &[
            "check",
            "--json",
            "--edit",
            "main.weight/body#0000",
            "{ 1 }",
        ],
        &dir,
    );
    assert_eq!(lock(&dir), None);
    let body = format!("main.weight/body#{}", hash("{ o * 2 }"));
    run(&["check", "--json", "--edit", &body, "{ o * 3 }"], &dir);
    assert_eq!(lock(&dir).unwrap(), pin(old, DOC));
}

#[test]
fn pins_name_tests_by_their_quoted_names_and_go_with_their_docs() {
    let source = "/// Adds one.\ntest \"adds one\" { assert 1 + 1 == 2 }\n";
    let dir = package("tests", source);
    run(&["fmt"], &dir);
    let line = format!(
        "main.\"adds one\" #{} #{}\n",
        hash("test \"adds one\" {}"),
        hash("/// Adds one.")
    );
    assert_eq!(lock(&dir).unwrap(), line);
    // A package with no doc left has no `docs.lock`.
    fs::write(
        dir.join("src/main.lt"),
        "test \"adds one\" { assert 1 + 1 == 2 }\n",
    )
    .unwrap();
    run(&["fmt"], &dir);
    assert_eq!(lock(&dir), None);
}

#[test]
fn a_program_without_a_manifest_has_no_docs_lock() {
    let dir = directory("docs-lock", "no-manifest");
    fs::write(dir.join("main.lt"), weight("fn weight(o: i64) -> i64", DOC)).unwrap();
    run(&["fmt"], &dir);
    assert_eq!(lock(&dir), None);
}
