//! `stilt lsp` while code is written (goal one-engine): completion of the names in scope,
//! of members after a `.`, of modules after `use` and of keywords, in code that doesn't parse
//! yet; the signature of the function a call calls; and formatting as `stilt fmt` formats.

mod common;

use common::editor::Editor;
use serde_json::{Value, json};

const SOURCE: &str = "type Order = { name: str, qty: i64 }\n\nimpl Order {\n  fn add(self, n: i64) -> i64 { self.qty + n }\n}\n\n/// The weight of an order.\nfn weight(o: Order) -> i64 { o.qty * 2 }\n\nfn main() / io {\n  let order = Order { name: \"a\", qty: 3 }\n  let w = weight(order)\n  print(\"{w}\")\n}\n";

/// The completion items offered at a position, after the buffer is set to `text`.
fn completions(editor: &mut Editor, text: &str, line: u64, character: u64) -> Vec<Value> {
    editor.change(text, false);
    let found = editor.at("textDocument/completion", line, character);
    found["items"].as_array().cloned().unwrap_or_default()
}

fn item<'a>(items: &'a [Value], label: &str) -> Option<&'a Value> {
    items.iter().find(|i| i["label"] == label)
}

#[test]
fn completion_offers_the_names_in_scope_with_their_types_and_docs() {
    let mut editor = Editor::open("complete_names", SOURCE);
    editor.change(SOURCE, true);
    let items = completions(&mut editor, SOURCE, 12, 2);
    let w = item(&items, "w").expect("a local");
    assert_eq!(w["detail"], "i64", "{w}");
    assert_eq!(w["kind"], 6);
    assert_eq!(item(&items, "order").unwrap()["detail"], "Order");
    let weight = item(&items, "weight").expect("an item");
    assert_eq!(weight["kind"], 3);
    assert_eq!(weight["detail"], "weight(o: Order) -> i64");
    assert_eq!(weight["documentation"]["value"], "The weight of an order.");
    assert_eq!(item(&items, "Order").unwrap()["kind"], 22);
    assert!(item(&items, "print").is_some(), "the prelude's");
    assert!(item(&items, "let").is_some(), "a statement's keyword");
    assert!(item(&items, "fn").is_none(), "no item keyword in a body");
}

#[test]
fn completion_offers_a_value_s_members_in_unfinished_code() {
    // The `.` leaves `main` with a syntax error, so the server checks it without the `.`.
    let mut editor = Editor::open("complete_members", SOURCE);
    editor.change(SOURCE, true);
    let typing = SOURCE.replace("  print(\"{w}\")\n", "  order.\n");
    let items = completions(&mut editor, &typing, 12, 8);
    let qty = item(&items, "qty").expect("a field");
    assert_eq!(qty["kind"], 5);
    assert_eq!(qty["detail"], "qty: i64");
    let add = item(&items, "add").expect("a method");
    assert_eq!(add["kind"], 2);
    assert_eq!(add["detail"], "add(self, n: i64) -> i64");
    assert!(item(&items, "len").is_none(), "no other type's method");
    let partial = SOURCE.replace("  print(\"{w}\")\n", "  order.na\n");
    let items = completions(&mut editor, &partial, 12, 10);
    assert!(item(&items, "name").is_some(), "{items:?}");
    let listed = SOURCE.replace("  print(\"{w}\")\n", "  [w].\n");
    let items = completions(&mut editor, &listed, 12, 6);
    assert!(item(&items, "len").is_some(), "a list's method");
}

#[test]
fn completion_offers_a_module_s_items_and_a_type_s_variants() {
    let shapes = "/// A shape.\npub type Shape = | Circle(f64) | Dot\n\npub fn area(s: Shape) -> f64 { 0.0 }\n\nfn hidden() -> i64 { 1 }\n";
    let source = "use shapes\n\nfn main() / io {\n  print(\"{shapes.area(shapes.Dot)}\")\n}\n";
    let mut editor = Editor::open_with("complete_modules", source, &[("shapes.lt", shapes)]);
    editor.change(source, true);
    let typing = source.replace("  print", "  shapes.\n  print");
    let items = completions(&mut editor, &typing, 3, 9);
    assert_eq!(
        item(&items, "area").unwrap()["detail"],
        "area(s: Shape) -> f64"
    );
    assert_eq!(
        item(&items, "Shape").unwrap()["documentation"]["value"],
        "A shape."
    );
    assert!(item(&items, "hidden").is_none(), "a private item");
    let typing = source.replace("  print", "  shapes.Shape.\n  print");
    let items = completions(&mut editor, &typing, 3, 15);
    assert_eq!(item(&items, "Circle").unwrap()["kind"], 20, "{items:?}");
    assert!(item(&items, "Dot").is_some());
}

#[test]
fn completion_offers_shape_and_name_after_a_type_where_std_meta_is_named() {
    // meta.shape-and-name: in a module that names `std.meta`, `T.shape()` and `T.name()`, after a
    // type parameter and after a declared type; in one that doesn't, nothing new.
    let source = "use std.meta\n\ntype Point = { x: i64 }\n\nfn named<T>(value: T) -> str {\n  T.name()\n}\n";
    let mut editor = Editor::open("complete_meta", source);
    editor.change(source, true);
    let typing = source.replace("  T.name()", "  T.\n  T.name()");
    let items = completions(&mut editor, &typing, 5, 4);
    assert!(item(&items, "shape").is_some(), "{items:?}");
    assert!(item(&items, "name").is_some(), "{items:?}");
    let typing = source.replace("  T.name()", "  Point.\n  T.name()");
    let items = completions(&mut editor, &typing, 5, 8);
    assert!(item(&items, "shape").is_some(), "{items:?}");
    let plain = "type Point = { x: i64 }\n\nfn main() {\n  Point.\n}\n";
    let items = completions(&mut editor, plain, 3, 8);
    assert!(item(&items, "shape").is_none(), "{items:?}");
}

#[test]
fn completion_offers_modules_after_use_and_item_keywords_at_the_top() {
    let mut editor = Editor::open("complete_use", SOURCE);
    editor.change(SOURCE, true);
    let typing = format!("use std.\n{SOURCE}");
    let items = completions(&mut editor, &typing, 0, 8);
    assert_eq!(item(&items, "view").unwrap()["kind"], 9, "{items:?}");
    assert!(item(&items, "prelude").is_none());
    let items = completions(&mut editor, SOURCE, 1, 0);
    assert!(item(&items, "fn").is_some());
    assert!(item(&items, "let").is_none());
}

#[test]
fn signature_help_shows_the_parameter_being_written() {
    let mut editor = Editor::open("signature", SOURCE);
    editor.change(SOURCE, true);
    let typing = SOURCE.replace("  print(\"{w}\")\n", "  let z = weight(\n");
    editor.change(&typing, false);
    let help = editor.at("textDocument/signatureHelp", 12, 17);
    let signature = &help["signatures"][0];
    assert_eq!(signature["label"], "weight(o: Order) -> i64", "{help}");
    assert_eq!(signature["parameters"], json!([{ "label": [7, 15] }]));
    assert_eq!(
        signature["documentation"]["value"],
        "The weight of an order."
    );
    assert_eq!(help["activeParameter"], 0);
    // A method's receiver is its first argument, written before the `.`.
    let typing = SOURCE.replace("  print(\"{w}\")\n", "  let z = order.add(\n");
    editor.change(&typing, false);
    let help = editor.at("textDocument/signatureHelp", 12, 20);
    assert_eq!(
        help["signatures"][0]["label"], "Order.add(self, n: i64) -> i64",
        "{help}"
    );
    assert_eq!(help["activeParameter"], 1);
    let help = editor.at("textDocument/signatureHelp", 10, 4);
    assert_eq!(help, Value::Null, "no call");
}

#[test]
fn formatting_formats_as_stilt_fmt_and_refuses_a_syntax_error() {
    let source = "fn main()/io{print(\"a\")}\n";
    let mut editor = Editor::open("format", source);
    editor.change(source, true);
    let edits = editor.about("textDocument/formatting", &json!({ "options": {} }));
    assert_eq!(
        edits[0]["newText"], "fn main() / io { print(\"a\") }\n",
        "{edits}"
    );
    assert_eq!(
        edits[0]["range"]["end"],
        json!({ "line": 1, "character": 0 })
    );
    editor.change("fn main() / io { print(\"a\") }\n", false);
    let edits = editor.about("textDocument/formatting", &json!({ "options": {} }));
    assert_eq!(edits, json!([]));
    editor.change("fn main() / io { print( }\n", false);
    let edits = editor.about("textDocument/formatting", &json!({ "options": {} }));
    assert_eq!(edits, Value::Null);
}

#[test]
fn completion_offers_when_and_the_items_of_std_par_and_std_sync() {
    // shared.when and shared.std-sync, and par.std-par.
    let source =
        "use std.par\nuse std.sync\n\nfn main() / io {\n  print(\"{par.map([1], |x| x)}\")\n}\n";
    let mut editor = Editor::open("complete_shared", source);
    editor.change(source, true);
    let items = completions(&mut editor, source, 4, 2);
    assert!(item(&items, "when").is_some(), "a statement's keyword");
    let typing = source.replace("  print", "  par.\n  print");
    let items = completions(&mut editor, &typing, 4, 6);
    for name in ["map", "each", "both", "fold"] {
        assert!(item(&items, name).is_some(), "{name}: {items:?}");
    }
    let typing = source.replace("  print", "  sync.\n  print");
    let items = completions(&mut editor, &typing, 4, 7);
    assert!(item(&items, "Shared").is_some(), "{items:?}");
}

#[test]
fn completion_offers_comptime_value_parameters_and_std_array() {
    // generics.value-parameters-in-body and generics.arrays, and meta.staging-annotations.
    let source = "use std.array\n\nfn sum<n: i64>(a: array.Array<i64, n>) -> i64 {\n  0\n}\n";
    let mut editor = Editor::open("complete_values", source);
    editor.change(source, true);
    let items = completions(&mut editor, source, 3, 2);
    assert!(item(&items, "comptime").is_some(), "a statement's keyword");
    assert!(item(&items, "n").is_some(), "a value parameter: {items:?}");
    let typing = source.replace("  0", "  array.\n  0");
    let items = completions(&mut editor, &typing, 3, 8);
    for name in ["Array", "fill", "from_list"] {
        assert!(item(&items, name).is_some(), "{name}: {items:?}");
    }
}
