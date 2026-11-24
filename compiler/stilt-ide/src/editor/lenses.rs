//! The code lenses of a file and their jobs: a lens on each test, doc example and property, read
//! off the file's syntax tree, that runs `stilt test --json` in the program, and one on the
//! `main` of the program's `main.lt` that runs `stilt run`. Both read the editor's buffers
//! through the program's engine, so a lens runs what the editor shows.

use std::path::Path;
use std::process::Command;

use serde_json::Value;
use stilt_lsp::{Job, Lens, Outcome, Output, Ran};
use stilt_syntax::SyntaxKind::{DOC_COMMENT, FN, NAME, TEST, TEST_KW};

/// The longest label a lens shows, in characters.
const LABEL: usize = 60;

/// The lenses of the file at `path`, whose text is `text`, in the program at `root`.
pub fn lenses(root: &Path, path: &Path, text: &str) -> Vec<Lens> {
    let tree = stilt_syntax::parse(text).syntax();
    let main = path == root.join("main.lt");
    let mut found = Vec::new();
    for token in tree
        .descendants_with_tokens()
        .filter_map(stilt_syntax::SyntaxElement::into_token)
        .filter(|t| t.kind() == DOC_COMMENT)
    {
        let doc = token.text().trim_start_matches('/').trim_start();
        if doc.starts_with("ex:") || doc.starts_with("prop:") {
            found.push(lens(token.text_range().start().into(), Job::Tests));
        }
    }
    for node in tree.children() {
        if node.kind() == TEST {
            let keyword = node
                .children_with_tokens()
                .find(|e| e.kind() == TEST_KW)
                .map_or(node.text_range(), |e| e.text_range());
            found.push(lens(keyword.start().into(), Job::Tests));
        }
        let named_main = || {
            node.children()
                .find(|c| c.kind() == NAME)
                .is_some_and(|n| n.text() == "main")
        };
        if main && node.kind() == FN && named_main() {
            found.push(lens(node.text_range().start().into(), Job::Main));
        }
    }
    found.sort_by_key(|l| l.at);
    found
}

fn lens(at: u32, job: Job) -> Lens {
    Lens { at, job }
}

/// The process that runs `job` in the program at `root`.
///
/// # Errors
///
/// Why it can't: the running `stilt` can't be found.
pub fn job(root: &Path, job: Job) -> Result<Command, String> {
    let stilt = std::env::current_exe().map_err(|e| format!("cannot find stilt: {e}"))?;
    let mut command = Command::new(stilt);
    match job {
        Job::Tests => command.args(["test", "--json", "."]),
        Job::Main => command.args(["run", "."]),
    };
    command.current_dir(root).env("NO_COLOR", "1");
    Ok(command)
}

/// What the process of `job` in the program at `root` found.
#[must_use]
pub fn ran(root: &Path, job: Job, output: &Output) -> Ran {
    match job {
        Job::Tests => tested(root, output),
        Job::Main => {
            let all = format!("{}{}", output.stdout, output.stderr);
            let last = all.lines().rfind(|l| !l.trim().is_empty());
            let status = output
                .code
                .map_or("stopped".to_owned(), |c| format!("exited with {c}"));
            let label = match last {
                Some(line) => short(&format!("{status} · {}", line.trim())),
                None => status.clone(),
            };
            let outcome = Outcome {
                at: None,
                passed: output.code == Some(0),
                label,
                detail: if all.is_empty() { status.clone() } else { all },
            };
            Ran {
                outcomes: vec![outcome],
                summary: format!("main {status}"),
            }
        }
    }
}

/// The results of `stilt test --json`, each at its case's file and line.
fn tested(root: &Path, output: &Output) -> Ran {
    let Ok(verdict) = serde_json::from_str::<Value>(&output.stdout) else {
        let why = if output.stderr.trim().is_empty() {
            "it was stopped"
        } else {
            output.stderr.trim()
        };
        return Ran {
            outcomes: Vec::new(),
            summary: format!("`stilt test` gave no verdict: {why}"),
        };
    };
    let tests = verdict["tests"].as_array().map_or(&[][..], Vec::as_slice);
    let outcomes: Vec<Outcome> = tests.iter().filter_map(|t| outcome(root, t)).collect();
    let failed = outcomes.iter().filter(|o| !o.passed).count();
    let error = (verdict["diagnostics"].as_array().into_iter().flatten())
        .find(|d| d["code"].as_str().is_some_and(|c| c.starts_with('E')));
    let summary = match error {
        Some(d) if outcomes.is_empty() => format!(
            "No test ran: {}:{}: {} [{}]",
            d["file"].as_str().unwrap_or_default(),
            d["line"],
            d["message"].as_str().unwrap_or_default(),
            d["code"].as_str().unwrap_or_default(),
        ),
        _ => format!("{} passed, {failed} failed", outcomes.len() - failed),
    };
    Ran { outcomes, summary }
}

/// The result of one case of `stilt test --json`.
fn outcome(root: &Path, test: &Value) -> Option<Outcome> {
    let file = root.join(test["file"].as_str()?);
    let file = file.canonicalize().unwrap_or(file);
    let line = u32::try_from(test["line"].as_u64()?).ok()?;
    let passed = test["passed"] == true;
    let why: Vec<&str> = (test["why"].as_array().into_iter().flatten())
        .filter_map(Value::as_str)
        .collect();
    let label = if passed {
        "passed".to_owned()
    } else {
        short(why.first().copied().unwrap_or("failed"))
    };
    let name = test["name"].as_str().unwrap_or_default();
    let detail = if passed {
        format!("{name}: passed")
    } else {
        format!("{name}: failed\n{}", why.join("\n"))
    };
    Some(Outcome {
        at: Some((file, line)),
        passed,
        label,
        detail,
    })
}

/// A line cut to [`LABEL`] characters, with `…` where it is cut.
fn short(line: &str) -> String {
    if line.chars().count() <= LABEL {
        return line.to_owned();
    }
    let cut: String = line.chars().take(LABEL - 1).collect();
    format!("{cut}…")
}
