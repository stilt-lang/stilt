//! The formatter's tests (syntax.formatter-tests).
//!
//! - Each input in `tests/format/`, `NAME.in.lt`, formats to the output paired with it,
//!   `NAME.out.lt`, whose layout follows syntax.format, and which formats to itself.
//! - Formatting the conformance suite, the guide's examples and generated programs is
//!   idempotent, and the formatted text has the tree that `parse --sexp` prints of the source.
//!   `just formatter` generates the programs in `target/fmt-generated` and runs the ignored
//!   test that reads them.

use std::fs;
use std::path::{Path, PathBuf};

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The tree form of a text without syntax errors (syntax.tree-form).
fn tree(text: &str) -> String {
    stilt_syntax::sexp::module(&stilt_syntax::parse(text).tree())
}

/// Where two texts first differ, by line.
fn difference(expected: &str, found: &str) -> String {
    let mut expected_lines = expected.lines();
    let mut found_lines = found.lines();
    for line in 1.. {
        match (expected_lines.next(), found_lines.next()) {
            (Some(e), Some(f)) if e == f => {}
            (None, None) => return "they differ only in their line endings".to_owned(),
            (e, f) => {
                return format!(
                    "line {line}: expected {:?}, found {:?}",
                    e.unwrap_or("<end>"),
                    f.unwrap_or("<end>")
                );
            }
        }
    }
    unreachable!("the lines run out")
}

#[test]
fn each_input_formats_to_its_output() {
    let dir = root().join("tests/format");
    let mut names: Vec<String> = fs::read_dir(&dir)
        .expect("tests/format")
        .map(|entry| entry.expect("an entry").path())
        .filter(|path| path.extension().is_some_and(|e| e == "lt"))
        .map(|path| {
            path.file_name()
                .expect("a name")
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    names.sort();
    let mut failures = Vec::new();
    let mut pairs = 0;
    for name in &names {
        let Some(stem) = name.strip_suffix(".in.lt") else {
            let stem = name.strip_suffix(".out.lt").unwrap_or(name);
            if !names.contains(&format!("{stem}.in.lt")) {
                failures.push(format!("{name}: no input is paired with it"));
            }
            continue;
        };
        let Ok(expected) = fs::read_to_string(dir.join(format!("{stem}.out.lt"))) else {
            failures.push(format!("{name}: no output is paired with it"));
            continue;
        };
        let input = fs::read(dir.join(name)).expect("the input");
        pairs += 1;
        match stilt_fmt::format(&input) {
            Ok(found) if found == expected => {}
            Ok(found) => failures.push(format!("{stem}: {}", difference(&expected, &found))),
            Err(error) => failures.push(format!("{stem}: not formatted: {error:?}")),
        }
        if stilt_fmt::format(expected.as_bytes()).as_ref() != Ok(&expected) {
            failures.push(format!("{stem}: the expected output isn't canonical"));
        }
        if tree(&String::from_utf8_lossy(&input)) != tree(&expected) {
            failures.push(format!("{stem}: the expected output has another tree"));
        }
    }
    assert!(pairs > 0, "tests/format holds no input");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// How formatting a suite went.
#[derive(Debug, Default)]
struct Tally {
    canonical: usize,
    rewritten: usize,
    /// Sources with a syntax error, which the formatter leaves as they are.
    refused: usize,
    failures: Vec<String>,
}

/// Formats each source, checking that formatting it again changes nothing, and that the
/// formatted text has the source's tree.
fn properties(sources: &[(String, Vec<u8>)]) -> Tally {
    let mut tally = Tally::default();
    for (name, source) in sources {
        let once = match stilt_fmt::format(source) {
            Ok(once) => once,
            Err(stilt_fmt::Error::Syntax(_)) => {
                tally.refused += 1;
                continue;
            }
            Err(error) => {
                tally
                    .failures
                    .push(format!("{name}: not formatted: {error:?}"));
                continue;
            }
        };
        match stilt_fmt::format(once.as_bytes()) {
            Ok(twice) if twice == once => {}
            Ok(twice) => tally.failures.push(format!(
                "{name}: formatting twice differs from formatting once, {}",
                difference(&once, &twice)
            )),
            Err(error) => tally.failures.push(format!(
                "{name}: the formatted text isn't formatted: {error:?}"
            )),
        }
        if tree(&String::from_utf8_lossy(source)) != tree(&once) {
            tally
                .failures
                .push(format!("{name}: the formatted text has another tree"));
        }
        if once.as_bytes() == source.as_slice() {
            tally.canonical += 1;
        } else {
            tally.rewritten += 1;
        }
    }
    tally
}

/// The `.lt` files under a directory, skipping the entries whose names start with `_` or `.`,
/// as the conformance runner does (conformance.location).
fn files(dir: &Path, out: &mut Vec<(String, Vec<u8>)>) {
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|error| panic!("{}: {error}", dir.display()))
        .map(|entry| entry.expect("an entry").path())
        .collect();
    entries.sort();
    for path in entries {
        let name = path.file_name().expect("a name").to_string_lossy();
        if name.starts_with('_') || name.starts_with('.') {
            continue;
        }
        if path.is_dir() {
            files(&path, out);
        } else if name.ends_with(".lt") {
            let source = fs::read(&path).expect("a source file");
            out.push((path.display().to_string(), source));
        }
    }
}

/// The Stilt examples of the guide: each fenced block whose info string starts with the word
/// `stilt`, as the conformance runner reads them, fragments included.
fn guide_examples() -> Vec<(String, Vec<u8>)> {
    let dir = root().join("docs/guide");
    let mut documents: Vec<PathBuf> = fs::read_dir(&dir)
        .expect("docs/guide")
        .map(|entry| entry.expect("an entry").path())
        .filter(|path| path.extension().is_some_and(|e| e == "md"))
        .collect();
    documents.sort();
    let mut examples = Vec::new();
    for document in documents {
        let text = fs::read_to_string(&document).expect("a document");
        let lines: Vec<&str> = text.lines().collect();
        let mut i = 0;
        while i < lines.len() {
            let Some(info) = lines[i].strip_prefix("```") else {
                i += 1;
                continue;
            };
            let close = (i + 1..lines.len())
                .find(|&j| lines[j].trim_end() == "```")
                .expect("a closed block");
            if info.split_whitespace().next() == Some("stilt") {
                let source: String = lines[i + 1..close]
                    .iter()
                    .flat_map(|l| [*l, "\n"])
                    .collect();
                examples.push((
                    format!("{}:{}", document.display(), i + 1),
                    source.into_bytes(),
                ));
            }
            i = close + 1;
        }
    }
    examples
}

/// Checks the properties of a suite, its sources shared among the machine's cores.
fn check(suite: &str, sources: &[(String, Vec<u8>)]) {
    let threads = std::thread::available_parallelism().map_or(1, usize::from);
    let tallies: Vec<Tally> = std::thread::scope(|scope| {
        let handles: Vec<_> = sources
            .chunks(sources.len().div_ceil(threads).max(1))
            .map(|chunk| scope.spawn(|| properties(chunk)))
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("a thread"))
            .collect()
    });
    let mut tally = Tally::default();
    for part in tallies {
        tally.canonical += part.canonical;
        tally.rewritten += part.rewritten;
        tally.refused += part.refused;
        tally.failures.extend(part.failures);
    }
    println!(
        "{suite}: {} canonical, {} not canonical, {} with syntax errors",
        tally.canonical, tally.rewritten, tally.refused
    );
    assert!(
        tally.canonical + tally.rewritten > 0,
        "{suite}: nothing was formatted"
    );
    assert!(tally.failures.is_empty(), "{}", tally.failures.join("\n"));
}

#[test]
fn formatting_the_conformance_suite_is_idempotent_and_keeps_its_trees() {
    let mut sources = Vec::new();
    files(&root().join("conformance"), &mut sources);
    check("the conformance suite", &sources);
}

#[test]
fn formatting_the_guide_is_idempotent_and_keeps_its_trees() {
    check("the guide's examples", &guide_examples());
}

#[test]
#[ignore = "it reads the programs that `just formatter` generates in target/fmt-generated, and runs there"]
fn formatting_generated_programs_is_idempotent_and_keeps_their_trees() {
    let mut sources = Vec::new();
    files(&root().join("target/fmt-generated"), &mut sources);
    check("generated programs", &sources);
}
