//! `stilt lsp` finding its way around a program (goal one-engine): the references to a
//! name across the program's files and their highlights in one, renaming them, which refuses
//! the standard library's names and keywords, and the declarations of a file, or of the
//! program, as symbols.

mod common;

use common::editor::{Editor, range};
use serde_json::{Value, json};

const SHAPES: &str = "pub type Shape = | Circle(f64) | Dot\n\npub fn area(s: Shape) -> f64 {\n  match s {\n    Circle(r) => r * r\n    Dot => 0.0\n  }\n}\n";

const SOURCE: &str = "use shapes\n\ntype Point = { x: i64, y: i64 }\n\nimpl Point {\n  fn norm(self) -> i64 { self.x * self.x + self.y * self.y }\n}\n\nfn main() / io {\n  let p = Point { x: 3, y: 4 }\n  let n = p.norm()\n  print(\"{n} {p.x} {shapes.area(shapes.Circle(1.0))}\")\n}\n";

fn open(name: &str) -> Editor {
    let mut editor = Editor::open_with(name, SOURCE, &[("shapes.lt", SHAPES)]);
    assert_eq!(editor.change(SOURCE, true), json!([]));
    editor
}

/// Each location's file and range, in order.
fn places(found: &Value) -> Vec<(String, Value)> {
    let mut all: Vec<(String, Value)> = (found.as_array().into_iter().flatten())
        .map(|l| {
            let uri = l["uri"].as_str().unwrap_or_default();
            let file = uri.rsplit('/').next().unwrap_or_default().to_owned();
            (file, l["range"].clone())
        })
        .collect();
    all.sort_by_key(|(f, r)| (f.clone(), r.to_string()));
    all
}

fn at(file: &str, line: u64, start: u64, end: u64) -> (String, Value) {
    (file.to_owned(), range(line, start, end))
}

#[test]
fn the_references_to_a_variable_are_in_its_function() {
    let mut editor = open("references_local");
    let context = json!({ "context": { "includeDeclaration": true } });
    let found = editor.at_with("textDocument/references", (9, 6), &context);
    let main = |line, start, end| at("main.lt", line, start, end);
    assert_eq!(
        places(&found),
        [main(10, 10, 11), main(11, 14, 15), main(9, 6, 7)]
    );
    let context = json!({ "context": { "includeDeclaration": false } });
    let found = editor.at_with("textDocument/references", (10, 10), &context);
    assert_eq!(places(&found).len(), 2, "{found}");
}

#[test]
fn the_references_to_a_field_are_its_reads_and_records() {
    let mut editor = open("references_field");
    let context = json!({ "context": { "includeDeclaration": true } });
    let found = editor.at_with("textDocument/references", (2, 15), &context);
    let main = |line, start, end| at("main.lt", line, start, end);
    let expected = [
        main(11, 16, 17),
        main(2, 15, 16),
        main(5, 30, 31),
        main(5, 39, 40),
        main(9, 18, 19),
    ];
    assert_eq!(places(&found), expected, "{found}");
}

#[test]
fn the_references_to_a_variant_are_in_every_file() {
    let mut editor = open("references_variant");
    let context = json!({ "context": { "includeDeclaration": true } });
    let found = editor.at_with("textDocument/references", (11, 40), &context);
    let expected = [
        at("main.lt", 11, 39, 45),
        at("shapes.lt", 0, 19, 25),
        at("shapes.lt", 4, 4, 10),
    ];
    assert_eq!(places(&found), expected, "{found}");
}

#[test]
fn a_highlight_marks_a_method_s_declaration_and_calls_in_the_file() {
    let mut editor = open("highlights");
    let found = editor.at("textDocument/documentHighlight", 10, 13);
    let ranges: Vec<Value> = (found.as_array().into_iter().flatten())
        .map(|h| h["range"].clone())
        .collect();
    assert_eq!(ranges, [range(5, 5, 9), range(10, 12, 16)], "{found}");
}

#[test]
fn a_rename_changes_every_file_and_refuses_the_library_s_names_and_keywords() {
    let mut editor = open("rename");
    let prepared = editor.at("textDocument/prepareRename", 10, 6);
    assert_eq!(
        prepared,
        json!({ "range": range(10, 6, 7), "placeholder": "n" })
    );
    let renamed = editor.at_with(
        "textDocument/rename",
        (11, 28),
        &json!({ "newName": "surface" }),
    );
    let changes = &renamed["changes"];
    let edits = |file: &str| changes[editor.uri_of(file)].clone();
    assert_eq!(
        edits("shapes.lt"),
        json!([{ "range": range(2, 7, 11), "newText": "surface" }]),
        "{renamed}"
    );
    assert_eq!(
        edits("main.lt"),
        json!([{ "range": range(11, 27, 31), "newText": "surface" }])
    );
    let uri = editor.uri();
    let position = |line, character| json!({ "line": line, "character": character });
    let params = |line, character| json!({ "textDocument": { "uri": uri }, "position": position(line, character) });
    let refused = editor.request("textDocument/prepareRename", &params(11, 3));
    let message = refused["error"]["message"].as_str().unwrap_or_default();
    assert!(message.contains("standard library"), "{refused}");
    let refused = editor.request("textDocument/prepareRename", &params(9, 3));
    let message = refused["error"]["message"].as_str().unwrap_or_default();
    assert!(message.contains("keyword"), "{refused}");
    let mut wrong = params(2, 6);
    wrong["newName"] = json!("point");
    let refused = editor.request("textDocument/rename", &wrong);
    assert!(refused["error"]["message"].as_str().is_some(), "{refused}");
}

#[test]
fn the_symbols_of_a_file_nest_members_and_the_program_s_match_a_query() {
    let mut editor = open("symbols");
    let found = editor.about("textDocument/documentSymbol", &json!({}));
    let outline: Vec<(Value, Value, Vec<Value>)> = (found.as_array().into_iter().flatten())
        .map(|s| {
            let children = (s["children"].as_array().into_iter().flatten())
                .map(|c| json!([c["name"], c["kind"]]))
                .collect();
            (s["name"].clone(), s["kind"].clone(), children)
        })
        .collect();
    let expected = vec![
        (
            json!("Point"),
            json!(23),
            vec![json!(["x", 8]), json!(["y", 8])],
        ),
        (json!("impl Point"), json!(5), vec![json!(["norm", 6])]),
        (json!("main"), json!(12), vec![]),
    ];
    assert_eq!(outline, expected, "{found}");
    assert_eq!(found[2]["detail"], "main() / io");
    assert_eq!(found[0]["selectionRange"], range(2, 5, 10));
    let found = editor.request("workspace/symbol", &json!({ "query": "ar" }))["result"].clone();
    let area = (found.as_array().into_iter().flatten())
        .find(|s| s["name"] == "area")
        .cloned()
        .unwrap_or_default();
    assert_eq!(area["kind"], 12, "{found}");
    assert_eq!(area["containerName"], "shapes");
    assert!(
        area["location"]["uri"]
            .as_str()
            .unwrap_or_default()
            .ends_with("shapes.lt")
    );
    let names: Vec<&Value> = (found.as_array().into_iter().flatten())
        .map(|s| &s["name"])
        .collect();
    assert!(!names.contains(&&json!("main")), "{found}");
}
