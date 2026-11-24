//! `stilt lsp` helping code read (goal one-engine): inlay hints of inferred types and facts
//! as `stilt show` writes them in (Inferred facts, "Seven commands"), semantic tokens, folding
//! and selection ranges, and where a position is: its module, its tier and its function.

mod common;

use common::editor::Editor;
use serde_json::{Value, json};

/// The text of a hint's label, which is a string or, for facts, parts.
fn label(hint: &Value) -> String {
    match &hint["label"] {
        Value::Array(parts) => parts.iter().filter_map(|p| p["value"].as_str()).collect(),
        other => other.as_str().unwrap_or_default().to_owned(),
    }
}

const HINTED: &str = "fn first(xs: List<i64>) -> i64 { xs[0] }\n\nfn main() / io {\n  let xs = [1, 2]\n  let f = |a| a + first(xs)\n  let typed: i64 = 1\n  print(\"{f(typed)}\")\n}\n";

#[test]
fn inlay_hints_show_inferred_types_and_facts() {
    let mut editor = Editor::open("hints", HINTED);
    editor.change(HINTED, true);
    let whole =
        json!({ "start": { "line": 0, "character": 0 }, "end": { "line": 8, "character": 0 } });
    let hints = editor.about("textDocument/inlayHint", &json!({ "range": whole }));
    let shown: Vec<(u64, u64, String, Value)> = (hints.as_array().into_iter().flatten())
        .map(|h| {
            let p = &h["position"];
            (
                p["line"].as_u64().unwrap(),
                p["character"].as_u64().unwrap(),
                label(h),
                h["kind"].clone(),
            )
        })
        .collect();
    // facts.visibility: an index can panic; types.inferred-per-body: a `let` without a type has
    // one.
    assert_eq!(
        shown[0],
        (0, 31, "[panic]".to_owned(), Value::Null),
        "{hints}"
    );
    assert!(
        shown.contains(&(3, 8, ": List<i64>".to_owned(), json!(1))),
        "{hints}"
    );
    assert!(
        shown.contains(&(4, 12, ": i64".to_owned(), json!(1))),
        "a closure's parameter"
    );
    assert!(
        !shown.iter().any(|(line, ..)| *line == 5),
        "a `let` that writes its type"
    );
    let facts = shown
        .iter()
        .find(|(line, ..)| *line == 2)
        .expect("main's facts");
    assert!(facts.2.contains("alloc"), "{facts:?}");
    let first_line =
        json!({ "start": { "line": 0, "character": 0 }, "end": { "line": 1, "character": 0 } });
    let hints = editor.about("textDocument/inlayHint", &json!({ "range": first_line }));
    // facts.visibility: the line that causes `panic` says so at its end, after the facts.
    let first: Vec<String> = (hints.as_array().into_iter().flatten())
        .map(label)
        .collect();
    assert_eq!(first.len(), 2, "{hints}");
    assert!(
        first[1].starts_with("// ") && first[1].contains("panic"),
        "{hints}"
    );
}

const TOKENS: &str = "syntax unless {\n  ($cond: expr) $body: block => if !($cond) $body\n}\n\n/// The origin.\n/// ex: origin().x == 0\nfn origin() -> Point { Point { x: 0, y: 0 } }\n\ntype Point = { x: i64, y: i64 }\n\nfn apply<e>(escaping f: fn(i64) -> i64 / e, x: i64) -> i64 / e { f(x) }\n\nfn main() / io {\n  var n = origin().x\n  unless!(n == 0) { print(\"n is {n}\") }\n  n = apply(|a| a + 1, n)\n}\n";

/// The semantic tokens of `main.lt`, each with its line, its column, its length, its type and
/// its modifiers by name.
fn tokens(editor: &mut Editor) -> Vec<(u64, u64, u64, String, Vec<String>)> {
    let legend = editor.capabilities["semanticTokensProvider"]["legend"].clone();
    let names = |key: &str| -> Vec<String> {
        (legend[key].as_array().into_iter().flatten())
            .map(|n| n.as_str().unwrap_or_default().to_owned())
            .collect()
    };
    let (types, modifiers) = (names("tokenTypes"), names("tokenModifiers"));
    let data = editor.about("textDocument/semanticTokens/full", &json!({}))["data"].clone();
    let numbers: Vec<u64> = (data.as_array().into_iter().flatten())
        .map(|n| n.as_u64().unwrap())
        .collect();
    let (mut line, mut column) = (0, 0);
    numbers
        .chunks(5)
        .map(|t| {
            line += t[0];
            column = if t[0] == 0 { column + t[1] } else { t[1] };
            let marks = (0..modifiers.len())
                .filter(|bit| t[4] & (1 << bit) != 0)
                .map(|bit| modifiers[bit].clone())
                .collect();
            (
                line,
                column,
                t[2],
                types[usize::try_from(t[3]).unwrap()].clone(),
                marks,
            )
        })
        .collect()
}

#[test]
fn semantic_tokens_tell_what_each_word_is() {
    let mut editor = Editor::open("tokens", TOKENS);
    editor.change(TOKENS, true);
    let found = tokens(&mut editor);
    let at = |line: u64, column: u64| -> (String, Vec<String>) {
        let t = found.iter().find(|t| t.0 == line && t.1 == column);
        t.map(|t| (t.3.clone(), t.4.clone())).unwrap_or_default()
    };
    let is = |sort: &str, marks: &[&str]| -> (String, Vec<String>) {
        (
            sort.to_owned(),
            marks.iter().map(|m| (*m).to_owned()).collect(),
        )
    };
    assert_eq!(at(0, 0), is("keyword", &[]), "{found:?}");
    assert_eq!(at(0, 7), is("macro", &["declaration"]));
    assert_eq!(at(1, 3), is("fragment", &[]));
    assert_eq!(at(1, 10), is("type", &["defaultLibrary"]));
    assert_eq!(at(4, 0), is("comment", &["documentation"]));
    assert_eq!(at(5, 4), is("keyword", &["documentation"]));
    assert_eq!(at(5, 8), is("function", &["documentation"]));
    assert_eq!(at(6, 3), is("function", &["declaration"]));
    assert_eq!(at(8, 5), is("type", &["declaration"]));
    assert_eq!(at(8, 15), is("property", &["declaration"]));
    assert_eq!(at(10, 9), is("rowVariable", &["declaration"]));
    assert_eq!(at(10, 21), is("parameter", &["declaration"]));
    assert_eq!(at(10, 41), is("rowVariable", &[]));
    assert_eq!(at(10, 65), is("parameter", &[]));
    // effects.rows: `io` is the built-in label of a row.
    assert_eq!(at(12, 12), is("effect", &["defaultLibrary"]));
    assert_eq!(at(13, 2), is("keyword", &[]));
    assert_eq!(at(13, 6), is("variable", &["declaration", "mutable"]));
    assert_eq!(at(13, 19), is("property", &[]));
    assert_eq!(at(14, 2), is("macro", &[]));
    assert_eq!(at(14, 8), is("macro", &[]));
    assert_eq!(at(14, 26), is("string", &[]));
    assert_eq!(at(14, 32), is("interpolation", &[]));
    assert_eq!(at(15, 6), is("function", &[]));
    assert_eq!(at(15, 13), is("parameter", &["declaration"]));
    assert_eq!(at(15, 2), is("variable", &["mutable"]));
}

#[test]
fn value_parameters_and_staging_read_as_written() {
    let source = "type Mod<p: u64> = { value: u64 }\n\nfn modulus<p: u64>(m: Mod<p>) -> u64 {\n  comptime if p > 1 { p } else { 1 }\n}\n";
    let mut editor = Editor::open("values", source);
    editor.change(source, true);
    let found = tokens(&mut editor);
    let at = |line: u64, column: u64| -> (String, Vec<String>) {
        let t = found.iter().find(|t| t.0 == line && t.1 == column);
        t.map(|t| (t.3.clone(), t.4.clone())).unwrap_or_default()
    };
    let parameter = |marks: &[&str]| -> (String, Vec<String>) {
        let marks = marks.iter().map(|m| (*m).to_owned()).collect();
        ("parameter".to_owned(), marks)
    };
    // generics.value-parameters-in-body and generics.value-arguments: a
    // value parameter where it is declared, in a type and in a body.
    assert_eq!(at(0, 9), parameter(&["declaration"]), "{found:?}");
    assert_eq!(at(2, 11), parameter(&["declaration"]));
    assert_eq!(at(2, 26), parameter(&[]));
    assert_eq!(at(3, 14), parameter(&[]));
    assert_eq!(at(3, 22), parameter(&[]));
    // meta.staging-annotations: `comptime` is a keyword.
    assert_eq!(at(3, 2), ("keyword".to_owned(), Vec::new()));
}

#[test]
fn a_bound_test_reads_as_a_type_parameter_and_its_traits() {
    let source =
        "fn shown<T>(value: T) -> str {\n  if T: Show + Eq { value.show() } else { \"?\" }\n}\n";
    let mut editor = Editor::open("bound_tests", source);
    editor.change(source, true);
    let found = tokens(&mut editor);
    let at = |line: u64, column: u64| -> String {
        let t = found.iter().find(|t| t.0 == line && t.1 == column);
        t.map(|t| t.3.clone()).unwrap_or_default()
    };
    // meta.bound-tests: the type parameter it tests, and the traits it names.
    assert_eq!(at(1, 5), "typeParameter", "{found:?}");
    assert_eq!(at(1, 8), "interface");
    assert_eq!(at(1, 15), "interface");
}

#[test]
fn a_procedural_macro_reads_as_a_macro_with_its_quote_and_splices() {
    let source = "meta use twice\nuse std.meta\n\npub macro double(e: meta.Expr) -> meta.Expr { quote { $e + $(e) } }\n\nfn main() {}\n";
    let twice = "use std.meta\n\npub macro one() -> meta.Expr { quote { 1 } }\n";
    let mut editor = Editor::open_with("procedural", source, &[("twice.lt", twice)]);
    editor.change(source, true);
    let found = tokens(&mut editor);
    let at = |line: u64, column: u64| -> (String, Vec<String>) {
        let t = found.iter().find(|t| t.0 == line && t.1 == column);
        t.map(|t| (t.3.clone(), t.4.clone())).unwrap_or_default()
    };
    let keyword = ("keyword".to_owned(), Vec::new());
    // macros.procedural-declarations, macros.meta-use and macros.quote: `meta` before `use`,
    // `macro` and its name, `quote`, and the splices' `$`.
    assert_eq!(at(0, 0), keyword, "{found:?}");
    assert_eq!(at(3, 4), keyword);
    assert_eq!(
        at(3, 10),
        ("macro".to_owned(), vec!["declaration".to_owned()])
    );
    assert_eq!(at(3, 46), keyword);
    assert_eq!(at(3, 54), ("fragment".to_owned(), Vec::new()));
    assert_eq!(at(3, 59), ("fragment".to_owned(), Vec::new()));
}

#[test]
fn folding_and_selection_ranges_follow_the_tree() {
    let source = "use std.view\nuse std.math\n\n/// One.\n/// Two.\nfn main() / io {\n  let xs = [\n    1,\n    2,\n  ]\n  print(\"{xs}\")\n}\n";
    let mut editor = Editor::open("folds", source);
    editor.change(source, true);
    let folds = editor.about("textDocument/foldingRange", &json!({}));
    let all = folds.as_array().cloned().unwrap_or_default();
    let has = |fold: Value| all.contains(&fold);
    assert!(
        has(json!({ "startLine": 0, "endLine": 1, "kind": "imports" })),
        "{folds}"
    );
    assert!(
        has(json!({ "startLine": 3, "endLine": 4, "kind": "comment" })),
        "{folds}"
    );
    assert!(has(json!({ "startLine": 5, "endLine": 10 })), "{folds}");
    assert!(has(json!({ "startLine": 6, "endLine": 8 })), "{folds}");
    let positions = json!({ "positions": [{ "line": 7, "character": 4 }] });
    let found = editor.about("textDocument/selectionRange", &positions);
    let first = &found[0];
    let span = |s: &Value| {
        (
            s["start"]["line"].clone(),
            s["start"]["character"].clone(),
            s["end"]["character"].clone(),
        )
    };
    assert_eq!(
        span(&first["range"]),
        (json!(7), json!(4), json!(5)),
        "{found}"
    );
    let mut outer = first;
    let mut depth = 0;
    while !outer["parent"].is_null() {
        outer = &outer["parent"];
        depth += 1;
    }
    assert!(depth >= 4, "{found}");
    assert_eq!(
        outer["range"]["start"],
        json!({ "line": 0, "character": 0 })
    );
}

#[test]
fn the_whereabouts_of_a_position_are_its_module_tier_and_function() {
    let source = "type Point = { x: i64 }\n\nimpl Point {\n  fn get(self) -> i64 { self.x }\n}\n\nfn main() / io { print(\"{Point { x: 1 }.get()}\") }\n";
    let mut editor = Editor::open("whereabouts", source);
    editor.change(source, true);
    let found = editor.at("stilt/whereabouts", 3, 26);
    assert_eq!(
        found,
        json!({ "module": "main", "tier": "core", "function": "main.Point.get" })
    );
    let found = editor.at("stilt/whereabouts", 0, 3);
    assert_eq!(found["function"], Value::Null);
}

const SHARED: &str = "use std.sync\n\nfn bump(a: sync.Shared<i64>) { when a { a += 1 } }\n\nfn calm(n: i64) -> i64 without locks { n }\n\nfn main() {}\n";

#[test]
fn a_when_shows_as_a_keyword_and_gives_its_function_locks() {
    // shared.when and shared.locks: `when` is a keyword, its names are writable places, and the
    // function that runs it has `locks`, which `without` names as it names an effect.
    let mut editor = Editor::open("shared_tokens", SHARED);
    editor.change(SHARED, true);
    let found = tokens(&mut editor);
    let at = |line: u64, column: u64| -> (String, Vec<String>) {
        let t = found.iter().find(|t| t.0 == line && t.1 == column);
        t.map(|t| (t.3.clone(), t.4.clone())).unwrap_or_default()
    };
    assert_eq!(
        at(2, 31),
        ("keyword".to_owned(), vec!["controlFlow".to_owned()]),
        "{found:?}"
    );
    assert_eq!(at(2, 36), ("parameter".to_owned(), vec![]));
    assert_eq!(
        at(2, 40),
        ("variable".to_owned(), vec!["mutable".to_owned()])
    );
    assert_eq!(
        at(4, 31),
        ("effect".to_owned(), vec!["defaultLibrary".to_owned()])
    );
    let whole =
        json!({ "start": { "line": 0, "character": 0 }, "end": { "line": 7, "character": 0 } });
    let hints = editor.about("textDocument/inlayHint", &json!({ "range": whole }));
    let facts: Vec<(u64, u64, String)> = (hints.as_array().into_iter().flatten())
        .filter(|h| h["label"].is_array())
        .map(|h| {
            let p = &h["position"];
            (
                p["line"].as_u64().unwrap(),
                p["character"].as_u64().unwrap(),
                label(h),
            )
        })
        .collect();
    // effects.overflow-effect: the block's `+=` can overflow.
    assert_eq!(facts, [(2, 29, "[overflow, locks]".to_owned())], "{hints}");
}

const WORDS: &str = "type Op = | Eq | Lt

impl Show for Op {
  fn show(self) -> str { if self == Eq { \"=\" } else { \"<\" } }
}

fn main() / io {
  let pair = (true, i64.MAX)
  print(\"{pair.1:>8}\\t{Eq}\")
  return
}
";

#[test]
fn keywords_literals_and_strings_read_by_what_they_are() {
    // lexical.keywords, lexical.string-literals and lexical.format-specs;
    // traits.implementing-trait: a keyword that directs control apart from one that declares,
    // `true`, `self`, a primitive type before its constant, a tuple's element, a string's escape
    // and format spec, and a variant whose name a trait shares.
    let mut editor = Editor::open("words", WORDS);
    editor.change(WORDS, true);
    let found = tokens(&mut editor);
    let at = |line: u64, column: u64| -> (String, Vec<String>) {
        let t = found.iter().find(|t| t.0 == line && t.1 == column);
        t.map(|t| (t.3.clone(), t.4.clone())).unwrap_or_default()
    };
    let is = |sort: &str, marks: &[&str]| -> (String, Vec<String>) {
        (
            sort.to_owned(),
            marks.iter().map(|m| (*m).to_owned()).collect(),
        )
    };
    assert_eq!(at(2, 10), is("keyword", &[]), "{found:?}");
    assert_eq!(at(3, 25), is("keyword", &["controlFlow"]));
    assert_eq!(at(3, 28), is("selfKeyword", &[]));
    assert_eq!(at(3, 36), is("enumMember", &[]));
    assert_eq!(at(7, 14), is("boolean", &[]));
    assert_eq!(at(7, 20), is("type", &["defaultLibrary"]));
    assert_eq!(at(8, 15), is("property", &[]));
    assert_eq!(at(8, 16), is("formatSpecifier", &[]));
    assert_eq!(at(8, 19), is("interpolation", &[]));
    assert_eq!(at(8, 20), is("escapeSequence", &[]));
    assert_eq!(at(8, 23), is("enumMember", &[]));
    assert_eq!(at(9, 2), is("keyword", &["controlFlow"]));
}
