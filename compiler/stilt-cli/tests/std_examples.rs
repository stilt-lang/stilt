//! The standard library's own tests (std.examples): every doc example of `std/` passes under
//! `stilt test --std`, every function that the rule covers has one, but those of `std.meta`
//! that take what only a macro's run makes (macros.tokens-and-code), and no program's `stilt test`
//! runs them.

mod common;

use std::fs;
use std::path::PathBuf;

use common::{file, stdout, stilt};
use serde_json::Value;

/// The numeric types whose methods are those of `i64` and `f64` at another width, which need
/// no examples of their own.
const OTHER_WIDTHS: [&str; 8] = ["i8", "i16", "i32", "u8", "u16", "u32", "u64", "f32"];

/// The library's sources, with their paths under `std/`.
fn sources() -> Vec<(String, String)> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../std");
    let mut found: Vec<(String, String)> = fs::read_dir(&dir)
        .expect("std/ is readable")
        .map(|e| e.expect("an entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "lt"))
        .map(|p| {
            let name = p.file_name().unwrap().to_string_lossy().into_owned();
            (name, fs::read_to_string(&p).expect("a source is readable"))
        })
        .collect();
    found.sort();
    found
}

/// The types of `std.meta` that a program's run never makes but as macros.outside-run says: a
/// function or a method that takes one has no example (macros.tokens-and-code).
const MACRO_VALUES: [&str; 14] = [
    "Span",
    "Token",
    "Kind",
    "Delim",
    "Tokens",
    "Text",
    "File",
    "Name",
    "Expr",
    "Pattern",
    "Type",
    "FieldInit",
    "Error",
    "Cursor",
];

/// Whether the declaration `line` of a `pub` function needs an example: its row doesn't hold
/// `io`, and it returns something other than `Never`.
fn needs_example(line: &str) -> bool {
    !(line.contains("/ io") || line.contains("/ {io") || line.contains("-> Never"))
}

/// Whether the declaration `line` of a function of `std.meta`, in an impl of `block` if it is a
/// method, takes a value that only a macro's run makes.
fn takes_macro_values(block: &str, line: &str) -> bool {
    let params = line
        .split_once('(')
        .and_then(|(_, rest)| rest.split_once(')'))
        .map_or("", |(params, _)| params);
    let named = params
        .split(|c: char| !c.is_alphanumeric() && c != '_')
        .any(|word| MACRO_VALUES.contains(&word));
    named || (MACRO_VALUES.contains(&block) && params.contains("self"))
}

#[test]
fn every_function_of_the_library_that_rule_4_covers_has_an_example() {
    let mut missing = Vec::new();
    for (name, text) in sources() {
        let lines: Vec<&str> = text.lines().collect();
        let mut block = "";
        for (i, line) in lines.iter().enumerate() {
            if let Some(rest) = line.strip_prefix("impl ") {
                block = rest.split([' ', '<', '{']).next().unwrap_or("");
            } else if !line.starts_with(' ') && !line.is_empty() {
                block = "";
            }
            let trimmed = line.trim_start();
            if !trimmed.starts_with("pub fn ") || !needs_example(trimmed) {
                continue;
            }
            if OTHER_WIDTHS.contains(&block)
                || (name == "meta.lt" && takes_macro_values(block, trimmed))
            {
                continue;
            }
            let docs = lines[..i]
                .iter()
                .rev()
                .take_while(|l| l.trim_start().starts_with("///"));
            if !docs
                .into_iter()
                .any(|l| l.trim_start().starts_with("/// ex:"))
            {
                missing.push(format!("std/{name}:{}: {trimmed}", i + 1));
            }
        }
    }
    assert!(
        missing.is_empty(),
        "functions without an example:\n{}",
        missing.join("\n")
    );
}

#[test]
fn every_example_of_the_library_passes() {
    let path = file("std-examples", "around", "fn main() {}\n");
    let output = stilt(&["test", "--std", "--json", path.to_str().unwrap()], None);
    let verdict: Value = serde_json::from_str(&stdout(&output)).expect("a JSON verdict");
    let tests = verdict["tests"].as_array().expect("a list of tests");
    assert!(tests.len() > 300, "{} examples", tests.len());
    let failed: Vec<&Value> = tests.iter().filter(|t| t["passed"] != true).collect();
    assert!(failed.is_empty(), "failed: {failed:?}");
    assert!(
        tests
            .iter()
            .all(|t| t["file"].as_str().is_some_and(|f| f.starts_with("std/")))
    );
    assert!(output.status.success());
}

#[test]
fn a_program_s_tests_hold_none_of_the_library_s() {
    let path = file("std-examples", "own", "/// ex: 1 + 1 == 2\nfn main() {}\n");
    let output = stilt(&["test", "--json", path.to_str().unwrap()], None);
    let verdict: Value = serde_json::from_str(&stdout(&output)).expect("a JSON verdict");
    let tests = verdict["tests"].as_array().expect("a list of tests");
    assert_eq!(tests.len(), 1, "{tests:?}");
    assert_eq!(tests[0]["file"], "main.lt");
}

#[test]
fn every_file_of_the_library_parses() {
    // A declaration with a syntax error is left out of its module, and a checked body that names
    // nothing of it never says so, so each file's syntax is checked here. `Task`'s `await` is the
    // one declaration that a keyword names (tasks.std-task).
    let broken: Vec<String> = sources()
        .iter()
        .flat_map(|(name, text)| {
            stilt_syntax::parse(text)
                .errors()
                .iter()
                .filter(|e| {
                    !(name == "task.lt"
                        && text.get(usize::from(e.range.start())..usize::from(e.range.end()))
                            == Some("await"))
                })
                .map(|e| format!("std/{name}: {e:?}"))
                .collect::<Vec<_>>()
        })
        .collect();
    assert!(broken.is_empty(), "{}", broken.join("\n"));
}
