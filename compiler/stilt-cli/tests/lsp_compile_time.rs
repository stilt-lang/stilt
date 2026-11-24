//! `stilt lsp` over the compile-time benchmark, `bench/compile-time/meta` (goal
//! editors-see-expansions). Each of its files is opened as an editor opens it, and the server
//! publishes no diagnostic for any file, so every macro use expands and every `comptime` form
//! (meta.staging-annotations) and reflective call (meta.static-reflection) checks without an error.
//! A hover over each macro use shows its expansion (macros.showing); a hover over a name of the
//! head of each `comptime` form, or of a `comptime match`'s first arm, shows what checking gave it;
//! and a hover over each reflective call shows the function it calls, with its `reflects` fact for
//! one of the program's (meta.reflects). The count of each is the one the benchmark's README gives.

mod common;

use std::path::Path;

use common::editor::Editor;
use serde_json::Value;

/// The benchmark's `regex!` uses, `comptime` forms and reflective calls, as its README counts
/// them.
const REGEX_USES: usize = 13;
const COMPTIME_FORMS: usize = 21;
const REFLECTIVE_CALLS: usize = 20;

/// The functions whose calls are the benchmark's reflective calls, as its code names them, and
/// whether each is the program's own, whose facts a hover shows.
const REFLECTING: [(&str, bool); 4] = [
    ("flat.pairs", true),
    ("table.render", true),
    ("json.to_text", false),
    ("json.from_text", false),
];

/// Each source file under `dir`, by its path from the benchmark's directory, with its text.
fn sources(dir: &Path, under: &str, found: &mut Vec<(String, String)>) {
    let mut entries: Vec<_> = (std::fs::read_dir(dir).expect("the benchmark is there"))
        .map(|e| e.expect("an entry").path())
        .collect();
    entries.sort();
    for path in entries {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        if path.is_dir() {
            sources(&path, &format!("{under}{name}/"), found);
        } else if path.extension().is_some_and(|e| e == "lt") {
            let text = std::fs::read_to_string(&path).expect("a source is UTF-8");
            found.push((format!("{under}{name}"), text));
        }
    }
}

/// The lines of `text` that hold code, by their numbers from 0: those that aren't comments.
fn code_lines(text: &str) -> impl Iterator<Item = (usize, &str)> {
    (text.lines().enumerate()).filter(|(_, l)| !l.trim_start().starts_with("//"))
}

/// The column of the byte `at` of `line`, as the protocol counts it, in UTF-16 units.
fn column(line: &str, at: usize) -> u64 {
    line[..at].encode_utf16().count() as u64
}

fn is_word(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// The bytes of `line` between `from` and `to` where a name or a keyword starts, each with it.
fn words(line: &str, from: usize, to: usize) -> Vec<(usize, &str)> {
    let mut found = Vec::new();
    let mut start = None;
    for (i, c) in line[from..to].char_indices().map(|(i, c)| (from + i, c)) {
        match (start, is_word(c)) {
            (None, true) if !c.is_ascii_digit() => start = Some(i),
            (Some(s), false) => {
                found.push((s, &line[s..i]));
                start = None;
            }
            _ => {}
        }
    }
    found.extend(start.map(|s| (s, &line[s..to])));
    found
}

/// The macro uses of `text`: the line of each, the column of its macro's name, and its path as
/// written, as `rx.regex`.
fn uses(text: &str) -> Vec<(usize, u64, String)> {
    let mut found = Vec::new();
    for (n, line) in code_lines(text) {
        for (i, _) in line.match_indices('!') {
            if !line[i + 1..].starts_with(['(', '[']) {
                continue;
            }
            let start = line[..i]
                .rfind(|c: char| !is_word(c) && c != '.')
                .map_or(0, |j| j + 1);
            let path = &line[start..i];
            if path.is_empty() {
                continue;
            }
            let name = start + path.rfind('.').map_or(0, |d| d + 1);
            found.push((n, column(line, name), path.to_owned()));
        }
    }
    found
}

/// The `comptime` forms of `text`: the line of each, and the byte its keyword starts at.
fn forms(text: &str) -> Vec<(usize, usize)> {
    let mut found = Vec::new();
    for (n, line) in code_lines(text) {
        let starts = line.match_indices("comptime ").map(|(i, _)| i);
        found.extend(
            starts
                .filter(|&i| !line[..i].ends_with(is_word))
                .map(|i| (n, i)),
        );
    }
    found
}

/// The reflective calls of `text`: the line of each, the column of the name of the function it
/// calls, the function as the code names it, and whether it is the program's own.
fn reflective(text: &str) -> Vec<(usize, u64, &'static str, bool)> {
    let mut found = Vec::new();
    for (n, line) in code_lines(text) {
        for (callee, own) in REFLECTING {
            let call = format!("{callee}(");
            let calls = line.match_indices(call.as_str()).map(|(i, _)| i);
            for i in calls.filter(|&i| !line[..i].ends_with(|c: char| is_word(c) || c == '.')) {
                let name = i + callee.rfind('.').map_or(0, |d| d + 1);
                found.push((n, column(line, name), callee, own));
            }
        }
    }
    found
}

/// Opens each file as an editor does, and checks that what the server publishes then, until it
/// publishes the file's own diagnostics, is empty.
fn open_each(editor: &mut Editor, files: &[(String, String)]) {
    for (path, text) in files {
        editor.open_document(path, text);
        let uri = editor.uri_of(path);
        loop {
            let published = editor.until(|m| m["method"] == "textDocument/publishDiagnostics");
            let params = &published["params"];
            let none = Value::Array(Vec::new());
            assert_eq!(
                params["diagnostics"], none,
                "after {path} is opened: {params}"
            );
            if params["uri"] == uri.as_str() {
                break;
            }
        }
    }
}

/// Whether a hover over a name of the head of the `comptime` form at byte `at` of line `n` of
/// `lines`, before the `{` of its body, or, for a `comptime match`, over a name of its first
/// arm's pattern, shows that name with what checking gave it.
fn form_checked(editor: &mut Editor, path: &str, lines: &[&str], (n, at): (usize, usize)) -> bool {
    let line = lines[n];
    let head = at + "comptime ".len();
    let end = line[head..].find('{').map_or(line.len(), |i| head + i);
    let mut spots: Vec<(usize, u64, &str)> = (words(line, head, end).into_iter())
        .map(|(i, w)| (n, column(line, i), w))
        .collect();
    if line[head..].starts_with("match ") {
        let arm = lines[n + 1];
        let end = arm.find("=>").unwrap_or(arm.len());
        spots.extend((words(arm, 0, end).into_iter()).map(|(i, w)| (n + 1, column(arm, i), w)));
    }
    spots.into_iter().any(|(l, c, word)| {
        let shown = editor.hover_in(path, l as u64, c);
        shown.starts_with("```stilt\n") && shown.contains(word)
    })
}

#[test]
fn the_server_expands_every_use_and_checks_every_compile_time_call_of_the_benchmark() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../bench/compile-time/meta");
    let mut files = Vec::new();
    sources(&dir, "", &mut files);
    let main = &files
        .iter()
        .find(|(p, _)| p == "main.lt")
        .expect("a main.lt")
        .1;
    let others: Vec<(&str, &str)> = (files.iter())
        .filter(|(p, _)| p != "main.lt")
        .map(|(p, t)| (p.as_str(), t.as_str()))
        .collect();
    let mut editor = Editor::open_with("compile_time", main, &others);
    open_each(&mut editor, &files);
    let (mut regex, mut expanded, mut staged, mut reflected) = (0, 0, 0, 0);
    for (path, text) in &files {
        for (line, character, macro_path) in uses(text) {
            let shown = editor.hover_in(path, line as u64, character);
            let named = format!("The expansion of `{macro_path}!`.");
            assert!(shown.contains(&named), "{path}:{}: {shown}", line + 1);
            expanded += 1;
            regex += usize::from(macro_path == "rx.regex");
        }
        let lines: Vec<&str> = text.lines().collect();
        for (line, at) in forms(text) {
            let checked = form_checked(&mut editor, path, &lines, (line, at));
            assert!(checked, "{path}:{}: {}", line + 1, lines[line]);
            staged += 1;
        }
        for (line, character, callee, own) in reflective(text) {
            let shown = editor.hover_in(path, line as u64, character);
            let name = callee.rsplit('.').next().expect("a name");
            let header = shown.contains(&format!("{name}<T>("));
            assert!(header, "{path}:{}: {shown}", line + 1);
            assert_eq!(
                own,
                shown.contains("reflects T"),
                "{path}:{}: {shown}",
                line + 1
            );
            reflected += 1;
        }
    }
    assert_eq!((regex, expanded), (REGEX_USES, REGEX_USES));
    assert_eq!(staged, COMPTIME_FORMS);
    assert_eq!(reflected, REFLECTIVE_CALLS);
}

#[test]
fn the_benchmark_s_uses_forms_and_calls_are_found_where_its_code_writes_them() {
    let text = "// rx.regex!(\"a\") in a comment\n\
                fn f<T>(xs: List<T>) -> str {\n  \
                  let m = rx.regex!(\"(a|b)\")\n  \
                  if !(xs.is_empty()) { 0 }\n  \
                  comptime for x in [1, 2] { print(\"{x}\") }\n  \
                  mytable.render(xs) + table.render(xs)\n\
                }\n";
    assert_eq!(uses(text), vec![(2, 13, "rx.regex".to_owned())]);
    assert_eq!(forms(text), vec![(4, 2)]);
    assert_eq!(reflective(text), vec![(5, 29, "table.render", true)]);
    assert_eq!(
        words("comptime for x in 0..n {", 9, 22),
        vec![(9, "for"), (13, "x"), (15, "in"), (21, "n")]
    );
}
