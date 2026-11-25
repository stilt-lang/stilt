//! `stilt lsp` (goal one-engine): diagnostics as the buffers change, with their fixes as code
//! actions (one-diagnostic-shape), their notes and their tags, hovers with inferred types, facts
//! and docs, and definitions, all answered by the program's engine, which the command line shares:
//! `check` reads the editor's buffers.

mod common;

use std::path::PathBuf;
use std::process::Command;
use std::time::{Duration, SystemTime};

use common::editor::{Editor, range};
use serde_json::{Value, json};

const SOURCE: &str = "type Order = { name: str, qty: i64 }\n\n/// The weight of an order.\nfn weight(o: Order) -> i64 { o.qty * 2 }\n\nfn first(xs: List<i64>) -> i64 { xs[0] }\n\nfn main() / io {\n  let order = Order { name: \"a\", qty: 3 }\n  let w = weight(order)\n  print(\"{w} {first([w])}\")\n}\n";

#[test]
fn a_buffer_s_diagnostics_come_with_their_fixes_and_clear_once_fixed() {
    let mut editor = Editor::open("diagnostics", SOURCE);
    let broken = SOURCE.replace("weight(order)", "wieght(order)");
    let diagnostics = editor.change(&broken, true);
    assert_eq!(diagnostics[0]["code"], "E0211", "{diagnostics}");
    assert_eq!(
        diagnostics[0]["range"]["start"],
        json!({ "line": 9, "character": 10 })
    );
    let range =
        json!({ "start": { "line": 9, "character": 11 }, "end": { "line": 9, "character": 11 } });
    let params = json!({ "textDocument": { "uri": editor.uri() }, "range": range, "context": { "diagnostics": [] } });
    let actions = editor.request("textDocument/codeAction", &params)["result"].clone();
    assert_eq!(actions[0]["title"], "write `weight`", "{actions}");
    let edits = &actions[0]["edit"]["changes"][editor.uri()];
    assert_eq!(edits[0]["newText"], "weight");
    assert_eq!(editor.change(SOURCE, false), json!([]));
}

#[test]
fn a_diagnostic_s_notes_are_related_and_its_warnings_are_marked() {
    // macros.errors-in-expansions: an error in a template is reported at the use, with a note at
    // the template. A hole (declarations.typed-holes) is information, and commented-out code
    // (lexical.commented-out-code) unnecessary.
    let source = "syntax twice {\n  ($x: expr) => $x + \"a\"\n}\n\n// let unused = 1\nfn later() -> i64 = ?\n\nfn main() / io { print(\"{twice!(1)} {later()}\") }\n";
    let mut editor = Editor::open("notes", source);
    let diagnostics = editor.change(source, true);
    let by = |code: &str| -> Value {
        let all = diagnostics.as_array().unwrap();
        all.iter()
            .find(|d| d["code"] == code)
            .cloned()
            .unwrap_or_default()
    };
    assert_eq!(by("W0001")["severity"], 2, "{diagnostics}");
    assert_eq!(by("W0001")["tags"], json!([1]));
    assert_eq!(by("W0300")["severity"], 3);
    let error = by("E0311");
    assert_eq!(error["severity"], 1);
    let related = &error["relatedInformation"][0];
    assert_eq!(related["message"], "`twice!` expands to this", "{error}");
    assert_eq!(related["location"]["uri"], editor.uri());
    assert_eq!(related["location"]["range"], range(1, 16, 24));
}

#[test]
fn the_command_line_reads_the_editor_s_buffers() {
    // one-engine: one engine, so `check` sees what the editor holds, saved or not.
    let mut editor = Editor::open("shared", SOURCE);
    let broken = SOURCE.replace("weight(order)", "wieght(order)");
    editor.change(&broken, true);
    let output = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["check", "--json", "."])
        .current_dir(&editor.dir)
        .output()
        .unwrap();
    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["diagnostics"][0]["code"], "E0211", "{report}");
}

#[test]
fn a_hover_shows_inferred_types_and_facts() {
    let mut editor = Editor::open("hover", SOURCE);
    editor.change(SOURCE, true);
    // A variable shows as its binding writes it, after `let` (expressions.let-else).
    assert_eq!(editor.hover(9, 6), "```stilt\nlet w: i64\n```");
    assert_eq!(
        editor.hover(9, 11),
        // effects.overflow-effect: `weight` multiplies.
        "```stilt\nweight(o: Order) -> i64 [overflow]\n```\n\nThe weight of an order."
    );
    // facts.visibility: an index can panic.
    assert_eq!(
        editor.hover(5, 3),
        "```stilt\nfirst(xs: List<i64>) -> i64 [panic]\n```"
    );
    assert_eq!(editor.hover(3, 32), "```stilt\nqty: i64\n```");
    assert_eq!(
        editor.hover(3, 14),
        "```stilt\ntype Order = { name: str, qty: i64 }\n```"
    );
}

#[test]
fn a_hover_renders_a_type_s_doc_and_its_examples() {
    // program.doc-examples: a doc's examples are code, shown as code after its text.
    let source = "/// A point on a grid.\n/// ex: Point { x: 1, y: 2 }.x == 1\ntype Point = { x: i64, y: i64 }\n\nfn main() / io { print(\"{Point { x: 1, y: 2 }.y}\") }\n";
    let mut editor = Editor::open("docs", source);
    editor.change(source, true);
    assert_eq!(
        editor.hover(2, 6),
        "```stilt\ntype Point = { x: i64, y: i64 }\n```\n\nA point on a grid.\n\n```stilt\nPoint { x: 1, y: 2 }.x == 1\n```"
    );
}

#[test]
fn a_hover_in_a_function_with_examples_shows_its_code() {
    // A function's doc examples are bodies of their own (program.doc-examples), in its doc comment,
    // and a position is in the body that starts last before it.
    let source = "/// Twice `n`.\n/// ex: twice(2) == 4\nfn twice(n: i64) -> i64 {\n  let m = n * 2\n  m\n}\n\nfn main() / io { print(\"{twice(1)}\") }\n";
    let mut editor = Editor::open("doc_examples", source);
    editor.change(source, true);
    assert_eq!(editor.hover(3, 6), "```stilt\nlet m: i64\n```");
    let example = editor.hover(1, 9);
    assert!(
        example.starts_with("```stilt\ntwice(n: i64) -> i64 [overflow]\n```"),
        "{example}"
    );
}

#[test]
fn a_hover_shows_a_once_parameter_in_the_facts() {
    // modes.show: the language server prints a `once` parameter as `show` does.
    let source =
        "fn run(f: fn() -> i64) -> i64 { f() }\n\nfn main() / io { print(\"{run(|| 1)}\") }\n";
    let mut editor = Editor::open("once", source);
    editor.change(source, true);
    assert_eq!(
        editor.hover(0, 3),
        "```stilt\nrun(f: fn() -> i64) -> i64 [once f]\n```"
    );
}

#[test]
fn a_hover_shows_the_parameter_a_result_views_in_the_facts() {
    // views.show: the language server prints the parameter a result views as `show` does.
    let source = "use std.view\n\nfn all(s: str) -> view.View<str> { view.View.all(s) }\n\nfn main() / io { print(\"{all(\"ab\").len()}\") }\n";
    let mut editor = Editor::open("views", source);
    editor.change(source, true);
    assert_eq!(
        editor.hover(2, 3),
        "```stilt\nall(s: str) -> view.View<str> [views s]\n```"
    );
}

#[test]
fn a_hover_shows_what_a_result_writes_and_a_projection_s_result() {
    // projections.show: the language server prints the `inout` parameter a result writes as
    // `show` does, and a projection's signature as written.
    let source = "use std.view\n\nfn head(inout xs: List<i64>) -> view.View<List<i64>> { view.into(inout xs, 0, 1) }\n\nfn at(inout xs: List<i64>, i: i64) -> inout i64 { yield xs[i] }\n\nfn main() / io {\n  var xs = [1, 2]\n  at(inout xs, 0) = 3\n  { var h = head(inout xs); h[0] = 4 }\n  print(\"{xs}\")\n}\n";
    let mut editor = Editor::open("projections", source);
    editor.change(source, true);
    assert_eq!(
        editor.hover(2, 3),
        "```stilt\nhead(inout xs: List<i64>) -> view.View<List<i64>> [writes xs, panic, alloc]\n```"
    );
    assert_eq!(
        editor.hover(4, 3),
        "```stilt\nat(inout xs: List<i64>, i: i64) -> inout i64 [panic, alloc]\n```"
    );
}

#[test]
fn a_definition_is_a_binding_or_a_declaration_s_name() {
    let mut editor = Editor::open("definition", SOURCE);
    editor.change(SOURCE, true);
    assert_eq!(
        editor.at("textDocument/definition", 9, 11)["range"],
        range(3, 3, 9)
    );
    assert_eq!(
        editor.at("textDocument/definition", 10, 10)["range"],
        range(9, 6, 7)
    );
    assert_eq!(
        editor.at("textDocument/definition", 3, 14)["range"],
        range(0, 5, 10)
    );
}

#[test]
fn a_variant_that_a_pattern_names_is_the_matched_type_s() {
    // patterns.variants-by-type: `Circle` names the variant of `shapes.Shape`, the type it is
    // matched against.
    let shapes = "pub type Shape = | Circle(f64) | Dot\n";
    let source = "use shapes\n\nfn area(s: shapes.Shape) -> f64 {\n  match s {\n    Circle(r) => r * r\n    Dot => 0.0\n  }\n}\n\nfn main() / io { print(\"{area(shapes.Dot)}\") }\n";
    let mut editor = Editor::open_with("variant", source, &[("shapes.lt", shapes)]);
    assert_eq!(editor.change(source, true), json!([]));
    assert_eq!(
        editor.hover(4, 5),
        "```stilt\npub type Shape = | Circle(f64) | Dot\n```"
    );
    assert_eq!(editor.hover(4, 11), "```stilt\nr: f64\n```");
    let found = editor.at("textDocument/definition", 4, 5);
    assert_eq!(found["range"], range(0, 9, 14));
    assert!(
        found["uri"].as_str().unwrap().ends_with("shapes.lt"),
        "{found}"
    );
}

#[test]
fn a_type_definition_is_the_declaration_of_a_variable_s_type() {
    let mut editor = Editor::open("type_definition", SOURCE);
    editor.change(SOURCE, true);
    let found = editor.at("textDocument/typeDefinition", 8, 6);
    assert_eq!(found["range"], range(0, 5, 10), "{found}");
    assert_eq!(found["uri"], editor.uri());
}

#[test]
fn a_hover_on_a_performance_shows_its_operation_and_effect() {
    // handlers.performing-operation: `Ask.ask()` performs the operation `ask` of the effect `Ask`.
    let source = "effect Ask {\n  fn ask() -> i64\n  fn tell(n: i64)\n}\n\nfn asked() -> i64 / Ask { Ask.ask() }\n\nfn main() / io {\n  with (handler Ask { fn ask() -> i64 { 1 }; fn tell(n: i64) {} }) { print(\"{asked()}\") }\n}\n";
    let mut editor = Editor::open("performance", source);
    assert_eq!(editor.change(source, true), json!([]));
    assert_eq!(
        editor.hover(5, 30),
        "```stilt\neffect Ask { fn ask() -> i64 }\n```"
    );
    let range =
        json!({ "start": { "line": 0, "character": 7 }, "end": { "line": 0, "character": 10 } });
    assert_eq!(editor.at("textDocument/definition", 5, 30)["range"], range);
}

#[test]
fn an_effect_is_in_the_outline_and_completion_with_its_operations() {
    // handlers.declaring-effect: an effect declares operations, which the outline nests under it.
    let source = "effect Ask {\n  fn ask() -> i64\n  fn tell(n: i64)\n}\n\nfn main() / io {\n  let n = 1\n  print(\"{n}\")\n}\n";
    let mut editor = Editor::open("effect_outline", source);
    assert_eq!(editor.change(source, true), json!([]));
    let found = editor.about("textDocument/documentSymbol", &json!({}));
    assert_eq!(found[0]["name"], "Ask", "{found}");
    assert_eq!(found[0]["kind"], 11);
    let operations: Vec<&Value> = (found[0]["children"].as_array().into_iter().flatten())
        .map(|c| &c["name"])
        .collect();
    assert_eq!(operations, [&json!("ask"), &json!("tell")], "{found}");
    let items = editor.at("textDocument/completion", 7, 2)["items"].clone();
    let ask = (items.as_array().into_iter().flatten())
        .find(|i| i["label"] == "Ask")
        .cloned()
        .unwrap_or_default();
    assert_eq!(ask["kind"], 8, "{items}");
    assert_eq!(ask["detail"], "effect Ask");
    assert!(
        (items.as_array().into_iter().flatten()).any(|i| i["label"] == "with"),
        "{items}"
    );
}

#[test]
fn a_server_whose_executable_another_build_replaces_stops() {
    // engines.toolchains: an update replaces the executable while the editor runs its server,
    // which can then reach no engine of its own build; it stops, and the editor starts the new
    // build's. A copy, since a link would share its time of change with every other test's.
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("replaced");
    std::fs::create_dir_all(&dir).unwrap();
    let exe = dir.join("stilt");
    // A new file each run: macOS kills an executable whose signed content changed in place, as
    // a copy over the last run's would once the compiler is rebuilt.
    let _ = std::fs::remove_file(&exe);
    std::fs::copy(env!("CARGO_BIN_EXE_stilt"), &exe).unwrap();
    let mut editor = Editor::open_from(&exe, "replaced", SOURCE);
    editor.change(SOURCE, true);
    assert_eq!(editor.hover(9, 6), "```stilt\nlet w: i64\n```");
    let later = SystemTime::now() + Duration::from_secs(60);
    // Opened to read: Linux refuses to open a running executable to write (ETXTBSY), and setting
    // the time needs only that the file is ours.
    let file = std::fs::File::open(&exe).unwrap();
    file.set_modified(later).unwrap();
    let changed = json!({
        "textDocument": { "uri": editor.uri(), "version": 2 },
        "contentChanges": [{ "text": SOURCE }],
    });
    editor.notify("textDocument/didChange", &changed);
    let status = editor.ended(Duration::from_secs(30));
    assert_eq!(status.and_then(|s| s.code()), Some(1), "the server runs on");
}
