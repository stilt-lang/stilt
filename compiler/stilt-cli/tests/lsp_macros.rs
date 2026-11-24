//! `stilt lsp` over procedural macros (macros.showing): the server expands every use, and
//! reports what its expansion's checking finds; a hover over a use shows its expansion; a use
//! whose macro failed stays as written, with its one diagnostic; and completion inside a use's
//! groups proceeds as in an expression of the use's scope, also while the macro fails on
//! unfinished input (goals editors-see-expansions and expansion-survives-broken-input).

mod common;

use common::editor::Editor;
use serde_json::Value;

const TWICE: &str = "use std.meta

/// The expression, doubled.
pub macro double(e: meta.Expr) -> meta.Expr { quote { $e + $e } }

/// The expression the use's tokens are, or an error at what follows it.
pub macro exactly(t: meta.Tokens) -> meta.Expr / raise<meta.Error> {
  var c = meta.cursor(t)
  let e = try c.expr()
  try c.end()
  quote { $e }
}
";

const SOURCE: &str = "meta use twice

type Order = { name: str, qty: i64 }

fn main() / io {
  let order = Order { name: \"a\", qty: 3 }
  let n = twice.double!(order.qty)
  print(\"{n}\")
}
";

fn open(name: &str) -> Editor {
    Editor::open_with(name, SOURCE, &[("twice.lt", TWICE)])
}

/// The completion items offered at a position, after the buffer is set to `text`.
fn completions(editor: &mut Editor, text: &str, line: u64, character: u64) -> Vec<Value> {
    editor.change(text, false);
    let found = editor.at("textDocument/completion", line, character);
    found["items"].as_array().cloned().unwrap_or_default()
}

fn labels(items: &[Value]) -> Vec<&str> {
    items.iter().filter_map(|i| i["label"].as_str()).collect()
}

#[test]
fn every_use_is_expanded_and_its_expansion_checked() {
    let mut editor = open("macros_expanded");
    assert_eq!(editor.change(SOURCE, true), Value::Array(Vec::new()));
    // The expansion adds two `i64`s, which a `bool` can't hold.
    let wrong = SOURCE.replace("let n = ", "let n: bool = ");
    let diagnostics = editor.change(&wrong, false);
    let found = diagnostics.as_array().expect("a list");
    assert_eq!(found.len(), 1, "{diagnostics}");
    assert_eq!(found[0]["range"]["start"]["line"], 6, "{diagnostics}");
}

#[test]
fn a_hover_over_a_use_shows_its_expansion() {
    let mut editor = open("macros_hover");
    editor.change(SOURCE, true);
    let shown = editor.hover(6, 18);
    assert!(shown.contains("(order.qty) + (order.qty)"), "{shown}");
    assert!(
        shown.contains("The expansion of `twice.double!`."),
        "{shown}"
    );
    // A name of the user's inside the use's groups is the user's, with its type.
    let order = editor.hover(6, 26);
    assert!(order.contains("order: Order"), "{order}");
}

#[test]
fn a_failed_use_stays_as_written_and_completes_inside_its_groups() {
    let mut editor = open("macros_failed");
    editor.change(SOURCE, true);
    let typing = SOURCE.replace("twice.double!(order.qty)", "twice.exactly!(order.)");
    // The macro raises at the `.`, and nothing follows from the use that failed.
    let diagnostics = editor.change(&typing, false);
    let found = diagnostics.as_array().expect("a list");
    assert_eq!(found.len(), 1, "{diagnostics}");
    assert_eq!(found[0]["code"], "E0225", "{diagnostics}");
    let shown = editor.hover(6, 18);
    assert!(!shown.contains("The expansion"), "{shown}");
    let items = completions(&mut editor, &typing, 6, 31);
    let members = labels(&items);
    assert!(members.contains(&"qty"), "{items:?}");
    assert!(members.contains(&"name"), "{items:?}");
}

#[test]
fn completion_inside_a_use_offers_the_names_of_its_scope() {
    let mut editor = open("macros_names");
    editor.change(SOURCE, true);
    let typing = SOURCE.replace("twice.double!(order.qty)", "twice.double!(or)");
    let items = completions(&mut editor, &typing, 6, 26);
    let names = labels(&items);
    assert!(names.contains(&"order"), "{items:?}");
    assert!(names.contains(&"Order"), "{items:?}");
}
