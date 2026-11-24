//! `stilt lsp`'s code lenses (goal one-engine): a lens that runs the program's tests above each
//! test and doc example, and one that runs `main`, each result shown inline beside its lens until
//! a file changes, and a lens that stops a job running.

mod common;

use common::editor::Editor;
use serde_json::{Value, json};

const TESTED: &str = "/// ex: double(2) == 4\nfn double(n: i64) -> i64 { n * 2 }\n\n\
                      fn main() / io {\n  print(\"doubled {double(21)}\")\n}\n\n\
                      test \"doubles\" {\n  assert double(3) == 6\n}\n\n\
                      test \"is wrong\" {\n  assert double(3) == 7\n}\n";

/// The lenses of `main.lt`, each as its line and its title.
fn lenses(editor: &mut Editor) -> Vec<(u64, String)> {
    let found = editor.about("textDocument/codeLens", &json!({}));
    (found.as_array().into_iter().flatten())
        .map(|l| {
            let line = l["range"]["start"]["line"].as_u64().unwrap_or(u64::MAX);
            let title = l["command"]["title"].as_str().unwrap_or_default();
            (line, title.to_owned())
        })
        .collect()
}

/// Runs a lens's command, and gives the message the job shows once it ends.
fn run(editor: &mut Editor, job: &str) -> String {
    let params = json!({ "command": "stilt.lens.run", "arguments": [job] });
    editor.request("workspace/executeCommand", &params);
    let shown = editor.until(|m| m["method"] == "window/showMessage");
    shown["params"]["message"]
        .as_str()
        .unwrap_or_default()
        .to_owned()
}

fn title(found: &[(u64, String)], line: u64, start: &str) -> bool {
    found
        .iter()
        .any(|(l, t)| *l == line && t.starts_with(start))
}

#[test]
fn lenses_run_the_tests_and_main_and_show_each_result_at_its_line() {
    let mut editor = Editor::open("lenses", TESTED);
    assert!(editor.capabilities["codeLensProvider"].is_object());
    editor.change(TESTED, true);
    let before = lenses(&mut editor);
    assert_eq!(
        before,
        [
            (0, "▶ Run tests".to_owned()),
            (3, "▶ Run".to_owned()),
            (7, "▶ Run tests".to_owned()),
            (11, "▶ Run tests".to_owned()),
        ]
    );
    // program.test-results: each case's result, the doc example's among them.
    assert_eq!(run(&mut editor, "tests"), "2 passed, 1 failed");
    let after = lenses(&mut editor);
    assert!(title(&after, 0, "✓ passed"), "{after:?}");
    assert!(title(&after, 7, "✓ passed"), "{after:?}");
    assert!(title(&after, 11, "✗ "), "{after:?}");
    assert_eq!(run(&mut editor, "main"), "main exited with 0");
    let after = lenses(&mut editor);
    assert!(
        title(&after, 3, "✓ exited with 0 · doubled 42"),
        "{after:?}"
    );
    // A result holds until a file changes.
    editor.change(&TESTED.replace("== 7", "== 6"), false);
    assert_eq!(lenses(&mut editor), before);
}

#[test]
fn the_lens_of_a_job_running_stops_it() {
    let source = "fn main() / io {\n  var n = 0\n  while true {\n    n = n + 1\n  }\n}\n";
    let client =
        json!({ "capabilities": { "workspace": { "codeLens": { "refreshSupport": true } } } });
    let mut editor = Editor::open_as("lenses_stop", source, &[], &client);
    editor.change(source, true);
    let params = json!({ "command": "stilt.lens.run", "arguments": ["main"] });
    editor.request("workspace/executeCommand", &params);
    assert_eq!(lenses(&mut editor), [(0, "■ Stop".to_owned())]);
    let stop = json!({ "command": "stilt.lens.stop", "arguments": [] });
    editor.request("workspace/executeCommand", &stop);
    let shown: Value = editor.until(|m| m["method"] == "window/showMessage");
    assert_eq!(shown["params"]["message"], "main stopped");
    // An editor that can be asked for the lenses again is, once the job ends.
    editor.until(|m| m["method"] == "workspace/codeLens/refresh");
    assert!(title(&lenses(&mut editor), 0, "✗ stopped"));
}

#[test]
fn visual_studio_code_is_offered_no_lenses() {
    let client = json!({ "capabilities": {}, "clientInfo": { "name": "Visual Studio Code" } });
    let editor = Editor::open_as("lenses_vscode", TESTED, &[], &client);
    assert!(editor.capabilities["codeLensProvider"].is_null());
    assert!(editor.capabilities["executeCommandProvider"].is_null());
}
