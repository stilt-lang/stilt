//! `stilt lsp` explaining code where it is written (goal one-engine): each inferred fact with
//! what it means and the lines that cause it, and each line's causes at its end, as `stilt show`
//! writes them (values.consumed-parameters; modes.show; facts.visibility); hovers over keywords,
//! effects, limits, primitive types and parameters; highlights that tell writes from reads; fixes
//! that apply alone or all at once; completions written as snippets; and diagnostics published
//! again when a file changes on disk.

mod common;

use common::editor::{Editor, range};
use serde_json::{Value, json};

const FACTS: &str = "fn first(xs: List<i64>) -> i64 { xs[0] }\n\nfn main() / io {\n  let xs = [1, 2]\n  print(\"{first(xs)}\")\n}\n";

#[test]
fn a_fact_says_what_it_means_and_goes_to_the_line_that_causes_it() {
    let mut editor = Editor::open("fact_parts", FACTS);
    editor.change(FACTS, true);
    let whole = json!({ "range": { "start": { "line": 0, "character": 0 }, "end": { "line": 6, "character": 0 } } });
    let hints = editor.about("textDocument/inlayHint", &whole);
    let all = hints.as_array().cloned().unwrap_or_default();
    let facts = all
        .iter()
        .find(|h| h["position"]["line"] == 0 && h["label"].is_array());
    let parts = facts.expect("first's facts")["label"].clone();
    let panic = (parts.as_array().into_iter().flatten())
        .find(|p| p["value"] == "panic")
        .cloned()
        .unwrap_or_default();
    // facts.visibility: an index can panic, and the hint shows the line that does, with what
    // facts.inferred-facts says of the fact.
    let tooltip = panic["tooltip"]["value"].as_str().unwrap_or_default();
    assert!(tooltip.starts_with("**`panic`**: Can panic"), "{parts}");
    assert!(
        tooltip.contains(&format!("[Line 1]({}#L1)", editor.uri())),
        "{tooltip}"
    );
    assert_eq!(panic["location"]["range"]["start"]["line"], 0, "{parts}");
    assert_eq!(parts[0]["value"], "[");
    let cause = all
        .iter()
        .find(|h| h["position"]["line"] == 0 && h["label"].is_string());
    let said = cause.expect("the line's cause")["label"]
        .as_str()
        .unwrap_or_default();
    assert!(said.starts_with("// ") && said.contains("panic"), "{hints}");
    assert_eq!(cause.unwrap()["paddingLeft"], true);
}

const HOVERED: &str = "fn bump(\n  n: i64,\n  inout xs: List<i64>,\n) / io {\n  var total = n\n  xs.push(total)\n  print(\"{total}\")\n}\n\nfn calm(n: i64) -> i64 without panic { n }\n\nfn main() / io {\n  var xs = [1]\n  bump(2, inout xs)\n}\n";

#[test]
fn every_word_of_the_language_explains_itself() {
    let mut editor = Editor::open("words_hover", HOVERED);
    editor.change(HOVERED, true);
    // lexical.keywords and lexical.primitive-type-names: a keyword, an effect of a row, a limit and
    // a primitive type each show the form they are written in and what they mean.
    let says = |shown: &str, what: &str| shown.contains(&format!("· {what}\n\n"));
    let fn_kw = editor.hover(0, 0);
    assert!(
        says(&fn_kw, "keyword") && fn_kw.contains("**`fn`**"),
        "{fn_kw}"
    );
    assert!(says(&editor.hover(3, 4), "effect"), "io");
    assert!(says(&editor.hover(9, 31), "limit"), "panic");
    assert!(says(&editor.hover(9, 23), "keyword"), "without");
    assert!(says(&editor.hover(9, 11), "type"), "i64");
    // A parameter where it is declared, and a variable as its binding writes it.
    assert_eq!(editor.hover(1, 2), "```stilt\nn: i64\n```");
    assert_eq!(editor.hover(2, 8), "```stilt\ninout xs: List<i64>\n```");
    assert_eq!(editor.hover(4, 6), "```stilt\nvar total: i64\n```");
}

#[test]
fn a_highlight_tells_where_code_writes_a_name_from_where_it_reads_it() {
    // modes.what-can-be-modified: a `var`'s binding and an `inout` argument write, the other uses
    // read.
    let mut editor = Editor::open("highlights", HOVERED);
    editor.change(HOVERED, true);
    let kinds = |found: &Value| -> Vec<(Value, Value)> {
        (found.as_array().into_iter().flatten())
            .map(|h| (h["range"]["start"]["line"].clone(), h["kind"].clone()))
            .collect()
    };
    let total = editor.at("textDocument/documentHighlight", 4, 6);
    assert_eq!(
        kinds(&total),
        [
            (json!(4), json!(3)),
            (json!(5), json!(2)),
            (json!(6), json!(2))
        ],
        "{total}"
    );
    let xs = editor.at("textDocument/documentHighlight", 12, 6);
    assert_eq!(
        kinds(&xs),
        [(json!(12), json!(3)), (json!(13), json!(3))],
        "{xs}"
    );
    assert_eq!(
        editor.at("textDocument/declaration", 13, 2)["range"],
        range(0, 3, 7)
    );
}

/// Two bodies, since a body reports its first error alone.
const MISSPELLED: &str = "fn weight(n: i64) -> i64 { n * 2 }\n\nfn a() -> i64 { wieght(1) }\n\nfn b() -> i64 { wieght(2) }\n\nfn main() / io { print(\"{a()} {b()}\") }\n";

#[test]
fn a_diagnostic_s_only_fix_is_preferred_and_a_file_s_fixes_apply_at_once() {
    let mut editor = Editor::open("fix_all", MISSPELLED);
    let diagnostics = editor.change(MISSPELLED, true);
    assert_eq!(
        diagnostics.as_array().map(Vec::len),
        Some(2),
        "{diagnostics}"
    );
    let at =
        json!({ "start": { "line": 2, "character": 17 }, "end": { "line": 2, "character": 17 } });
    let quick = editor.about(
        "textDocument/codeAction",
        &json!({ "range": at, "context": { "diagnostics": [], "only": ["quickfix"] } }),
    );
    assert_eq!(quick.as_array().map(Vec::len), Some(1), "{quick}");
    assert_eq!(quick[0]["isPreferred"], true);
    let whole =
        json!({ "start": { "line": 0, "character": 0 }, "end": { "line": 7, "character": 0 } });
    let only = json!(["source.fixAll.stilt"]);
    let all = editor.about(
        "textDocument/codeAction",
        &json!({ "range": whole, "context": { "diagnostics": [], "only": only } }),
    );
    assert_eq!(all.as_array().map(Vec::len), Some(1), "{all}");
    assert_eq!(all[0]["kind"], "source.fixAll.stilt");
    let edits = all[0]["edit"]["changes"][editor.uri()].clone();
    let texts: Vec<&Value> = (edits.as_array().into_iter().flatten())
        .map(|e| &e["newText"])
        .collect();
    assert_eq!(texts, [&json!("weight"), &json!("weight")], "{all}");
}

const COMPLETED: &str = "fn weight(n: i64, scale: i64) -> i64 { n * scale }\n\ntype Shape = | Circle(f64) | Dot\n\nfn main() / io {\n  let s = Shape.\n  let w = w\n}\n";

#[test]
fn a_completion_writes_a_call_a_variant_and_a_construct_as_snippets() {
    let client = json!({
        "capabilities": { "textDocument": { "completion": { "completionItem": {
            "snippetSupport": true, "labelDetailsSupport": true } } } },
        "clientInfo": { "name": "Visual Studio Code" },
    });
    let mut editor = Editor::open_as("snippets", COMPLETED, &[], &client);
    editor.change(COMPLETED, true);
    let item = |items: &Value, label: &str| -> Value {
        (items.as_array().into_iter().flatten())
            .find(|i| i["label"] == label)
            .cloned()
            .unwrap_or_default()
    };
    let named = editor.at("textDocument/completion", 6, 11)["items"].clone();
    let weight = item(&named, "weight");
    assert_eq!(
        weight["insertText"], "weight(${1:n}, ${2:scale})$0",
        "{weight}"
    );
    assert_eq!(weight["insertTextFormat"], 2);
    assert_eq!(
        weight["labelDetails"]["detail"],
        "(n: i64, scale: i64) -> i64"
    );
    assert_eq!(
        weight["command"]["command"],
        "editor.action.triggerParameterHints"
    );
    let construct = item(&named, "match");
    assert_eq!(
        construct["insertText"],
        "match ${1:value} {\n  ${2:pattern} => $0\n}"
    );
    assert_eq!(construct["detail"], "match value { pattern => … }");
    let members = editor.at("textDocument/completion", 5, 16)["items"].clone();
    assert_eq!(
        item(&members, "Circle")["insertText"],
        "Circle(${1:f64})$0",
        "{members}"
    );
    assert_eq!(item(&members, "Dot")["insertText"], Value::Null);
}

#[test]
fn a_change_on_disk_publishes_the_diagnostics_again() {
    // goal one-engine: the engine reads the disk as it answers, so a watched file's change
    // checks the program again, whatever made it.
    let util = "pub fn one() -> i64 { 1 }\n";
    let source = "use util\n\nfn main() / io { print(\"{util.one()}\") }\n";
    let mut editor = Editor::open_with("watched", source, &[("util.lt", util)]);
    assert_eq!(editor.change(source, true), json!([]));
    std::fs::write(
        editor.dir.join("util.lt"),
        "pub fn one() -> i64 { \"a\" }\n",
    )
    .unwrap();
    let changes = json!({ "changes": [{ "uri": editor.uri_of("util.lt"), "type": 2 }] });
    editor.notify("workspace/didChangeWatchedFiles", &changes);
    let uri = editor.uri_of("util.lt");
    let published = editor.until(|m| {
        m["method"] == "textDocument/publishDiagnostics"
            && m["params"]["uri"] == uri
            && m["params"]["diagnostics"]
                .as_array()
                .is_some_and(|d| !d.is_empty())
    });
    assert_eq!(
        published["params"]["diagnostics"][0]["code"], "E0311",
        "{published}"
    );
}
