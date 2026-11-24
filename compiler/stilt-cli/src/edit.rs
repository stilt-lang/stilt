//! `check --edit` and `test --edit`: edits addressed by a path and a hash (edits.command-line,
//! edits.refusals and edits.writing).
//!
//! - **Checking.** Every edit is checked against the files as they are on disk ([`resolve`]),
//!   each read under a shared lock, so that no other command's write is seen midway: its
//!   address, the part it names, its hash and its new text. If any edit is refused, none
//!   applies, no file changes and there is no verdict: the command gives each edit's result and
//!   exits with status 2, as `show` does for an address that names nothing.
//! - **Writing.** Otherwise the edits apply, each file locked while it is checked again and
//!   written ([`write`]), the docs of the packages they change are pinned (docs.writing-pins), and
//!   the command gives its verdict on the edited program, with the result of each edit.
//! - **Results.** With `--json`, the list `edits` in the object the command writes; without it,
//!   each refusal rendered on stderr, or `applied ADDRESS -> #HASH` for each edit that
//!   applied, before the verdict.

mod load;
mod refusal;
mod resolve;
mod results;
mod write;

use std::fmt::Write as _;
use std::io::Read as _;
use std::path::Path;

use serde_json::{Value, json};

use crate::report::Report;
pub(crate) use load::Loaded;
use resolve::{Raw, resolve};
use results::EditResult;

/// The edits of a command line, whose arguments alternate an address and a text.
pub(crate) fn pairs(args: &[String]) -> Vec<Raw> {
    args.as_chunks::<2>()
        .0
        .iter()
        .map(|[at, text]| Raw {
            at: at.clone(),
            text: text.clone(),
        })
        .collect()
}

/// Applies the edits `args` give to the program at `path`, then reports as `verdict` does,
/// adding the edits' results. With no edits, it is the verdict alone.
pub(crate) fn apply(
    args: &[String],
    path: &Path,
    json: bool,
    verdict: impl FnOnce() -> Report,
) -> Report {
    if args.is_empty() {
        return verdict();
    }
    let raws = pairs(args);
    let mut stdin = String::new();
    if raws.iter().any(|r| r.text == "-") {
        let _ = std::io::stdin().read_to_string(&mut stdin);
    }
    let done = match run(path, &raws, &stdin) {
        Ok(done) => done,
        Err(message) => return Report::refuse(&message),
    };
    let results: Vec<Value> = done.results.iter().map(EditResult::json).collect();
    if done.refused {
        return Report {
            stdout: if json {
                format!("{}\n", serde_json::json!({ "edits": results }))
            } else {
                String::new()
            },
            stderr: done.rendered,
            status: 2,
        };
    }
    let mut report = verdict();
    if json {
        report.stdout = with_edits(&report.stdout, results);
    } else {
        report.stderr = format!("{}{}", done.rendered, report.stderr);
    }
    report
}

/// The object `stdout` holds, with the list `edits`.
fn with_edits(stdout: &str, edits: Vec<Value>) -> String {
    let mut object: Value = serde_json::from_str(stdout).unwrap_or_else(|_| json!({}));
    object["edits"] = Value::Array(edits);
    format!("{object}\n")
}

/// What became of the edits of a command.
struct Done {
    results: Vec<EditResult>,
    /// Whether any edit was refused, so that none applied.
    refused: bool,
    /// The refusals rendered, or the lines that say which edits applied.
    rendered: String,
}

/// Checks the edits, and applies them when none is refused. Edits that find a file changed
/// between checking and writing are checked again against it.
fn run(path: &Path, raws: &[Raw], stdin: &str) -> Result<Done, String> {
    loop {
        let loaded = Loaded::read(path)?;
        let found = resolve(&loaded, raws, stdin);
        if found.iter().any(Result::is_err) {
            return Ok(refused(&loaded, raws, &found));
        }
        let ready: Vec<&resolve::Ready> = found.iter().filter_map(|r| r.as_ref().ok()).collect();
        let written = write::commit(&loaded, &ready)
            .map_err(|e| format!("cannot write the edited files: {e}"))?;
        let Some(now) = written else {
            continue;
        };
        let targets: Vec<(usize, usize)> = ready
            .iter()
            .map(|r| (r.target.file, r.target.part))
            .collect();
        let packages = targets
            .iter()
            .map(|&(f, _)| loaded.files[f].package)
            .collect();
        let mut rendered = String::new();
        // The edits applied, so a `docs.lock` that can't be written takes nothing back.
        if let Err(message) =
            crate::docs::pin(path, &packages, &crate::docs::before(&loaded, &targets))
        {
            let _ = writeln!(rendered, "stilt: {message}");
        }
        let mut results = Vec::new();
        for ((raw, r), now) in raws.iter().zip(&ready).zip(now) {
            let _ = r;
            if let Some(now) = &now {
                let hash = now.rsplit_once('#').map_or("", |(_, h)| h);
                let _ = writeln!(rendered, "applied {} -> #{hash}", raw.at);
            }
            results.push(EditResult {
                at: raw.at.clone(),
                applied: true,
                now,
                refused: None,
                syntax: None,
            });
        }
        return Ok(Done {
            results,
            refused: false,
            rendered,
        });
    }
}

/// The results and the rendering of edits of which some are refused.
fn refused(
    loaded: &Loaded,
    raws: &[Raw],
    found: &[Result<resolve::Ready, resolve::Refusal>],
) -> Done {
    let refusals: Vec<Option<&resolve::Refusal>> = found.iter().map(|r| r.as_ref().err()).collect();
    let mut rendered: Vec<String> = Vec::new();
    let mut results = Vec::new();
    for (i, (raw, r)) in raws.iter().zip(found).enumerate() {
        let Err(r) = r else {
            results.push(EditResult {
                at: raw.at.clone(),
                applied: false,
                now: None,
                refused: None,
                syntax: None,
            });
            continue;
        };
        let skip = matches!(&r.why, resolve::Why::Overlap(o) if refusal::repeats(i, *o, &refusals));
        if !skip {
            rendered.push(refusal::render(i + 1, raws, r, loaded));
        }
        results.push(EditResult {
            at: raw.at.clone(),
            applied: false,
            now: r.now.clone(),
            refused: Some(r.code.as_str()),
            syntax: match &r.why {
                resolve::Why::Text(s) => s.clone(),
                _ => None,
            },
        });
    }
    Done {
        results,
        refused: true,
        rendered: rendered.join("\n"),
    }
}
