//! The snapshot tests of diagnostics (goals one-diagnostic-shape and reviewed-messages). Each
//! program under `tests/diagnostics/` makes the compiler report one diagnostic, of the code its
//! name starts with, and what `stilt check` renders must equal the snapshot beside it. A snapshot
//! is a reviewed rendering: drafts wait in `_pending/` until `just snapshots-accept` moves them up,
//! so that no message changes without a review. Each fix that a snapshot offers is applied to a
//! copy of its program, through `check --edit`, which must then check without any diagnostic (goal
//! working-fixes; edits.fixes-as-edits). A fix that changes text outside every part has no edits in
//! the JSON, so it is applied through its change itself.
//!
//! A refusal of an edit (edits.refusals) has no diagnostic of the program, so its program has
//! a file of the same name with the extension `edits` beside it: the edits of its command, an
//! address on one line and the new text on the next, for each. `check --edit` on the program
//! must refuse one of them with the code its name starts with, and render what the snapshot
//! holds.
//!
//! A program whose dependencies are fetched (packages.fetching and packages.content-hash) has a
//! fixture `NAME.repos` beside it: a directory for each repository, whose directories, each named
//! by a version, hold the trees it tags. Its manifests name a repository `R` as `file:///repos/R`.
//! The harness builds the repositories in a directory of this run's own, under the system's
//! temporary directory, and checks a copy of the program whose manifests give their URLs there; in
//! what the copy renders, it spells them `file:///repos/R` again, wrapping the prose that holds
//! them as the renderer does, so that a snapshot reads the same on every machine. Each program is
//! checked with an empty cache of its own, once to fetch what it needs and then for its rendering,
//! which reports nothing fetched.

mod common;
mod record_shape;
mod repos;

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::Value;
use stilt_diag::{Code, codes};

/// The phases of the registry (errors.registry-phases), whose every code needs a snapshot.
const PHASES: [&str; 6] = [
    "syntax", "items", "types", "analyses", "warnings", "refusal",
];

/// The tier whose every code needs a snapshot.
const TIER: &str = "core";

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/diagnostics")
}

/// The programs approved and drafted: each `.lt` file, and each directory, which holds a
/// program.
fn programs() -> Vec<PathBuf> {
    let mut all = Vec::new();
    for dir in [root(), root().join("_pending")] {
        let Ok(entries) = fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.map(|e| e.expect("the directory is readable").path()) {
            let name = entry.file_name().unwrap_or_default().to_string_lossy();
            let fixture = entry.extension().is_some_and(|e| e == "repos");
            let program =
                (entry.is_dir() && !fixture) || entry.extension().is_some_and(|e| e == "lt");
            if program && !name.starts_with(['_', '.']) {
                all.push(entry);
            }
        }
    }
    all.sort();
    all
}

/// The code that a program's name starts with, such as E0208 for `E0208_twice.lt`.
fn named_code(program: &Path) -> Option<Code> {
    let name = program.file_name()?.to_string_lossy();
    Code::lookup(name.split('_').next()?)
}

/// The program that `path` checks: itself, or the program that a copy made by [`prepare`] is of.
fn named(path: &Path) -> PathBuf {
    match path.file_name() {
        Some(name) if name == "program" => path.parent().unwrap_or(path).to_path_buf(),
        _ => path.to_path_buf(),
    }
}

/// The cache of fetched packages of a program and of the copies made of it.
fn cache(program: &Path) -> PathBuf {
    let name = program.file_name().expect("a program has a name");
    Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("diagnostics-cache")
        .join(name)
}

/// The spelling of the URLs of a fixture's repositories in a program and in its snapshot.
const REPOS: &str = "file:///repos/";

/// A program readied to be checked: the path to check, and the URL of the directory that holds
/// its fixture's repositories in this run, if it has a fixture.
struct Prepared {
    path: PathBuf,
    repos: Option<String>,
}

impl Prepared {
    /// What the program renders, with the URLs of its repositories spelled as its snapshot
    /// spells them, and each paragraph of prose that holds one wrapped again.
    fn shown(&self, rendered: &[u8]) -> Vec<u8> {
        let text = String::from_utf8_lossy(rendered).into_owned();
        let Some(repos) = &self.repos else {
            return rendered.to_vec();
        };
        let paragraphs: Vec<String> = text
            .split("\n\n")
            .map(|p| {
                if !p.contains(repos.as_str()) {
                    return p.to_owned();
                }
                if p.lines().any(|l| l.starts_with("  ")) {
                    return p.replace(repos.as_str(), REPOS);
                }
                let end = if p.ends_with('\n') { "\n" } else { "" };
                let joined = p
                    .lines()
                    .collect::<Vec<_>>()
                    .join(" ")
                    .replace(repos.as_str(), REPOS);
                format!("{}{end}", stilt_diag::wrap(&joined).trim_end_matches('\n'))
            })
            .collect();
        paragraphs.join("\n\n").into_bytes()
    }
}

/// Readies a program to be checked, its cache emptied. A program with a fixture is copied into
/// a directory of this run's own, beside the repositories built from the fixture, and its
/// manifests in the copy name them there.
fn prepare(program: &Path) -> Prepared {
    let _ = fs::remove_dir_all(cache(program));
    let fixture = program.with_extension("repos");
    if !fixture.is_dir() {
        return Prepared {
            path: program.to_path_buf(),
            repos: None,
        };
    }
    let name = program.file_name().expect("a program has a name");
    let run = std::env::temp_dir()
        .join(format!("stilt-diagnostics-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&run);
    repos::build(&fixture, &run.join("repos"));
    let path = run.join("program");
    copy_all(program, &path);
    let repos = format!("file://{}/", run.join("repos").display());
    point(&path, &repos);
    Prepared {
        path,
        repos: Some(repos),
    }
}

/// Gives each manifest under `dir` the URLs of the repositories under `repos`.
fn point(dir: &Path, repos: &str) {
    for entry in fs::read_dir(dir).expect("the copy is readable") {
        let path = entry.expect("the copy is readable").path();
        if path.is_dir() {
            point(&path, repos);
        } else if path.file_name().is_some_and(|n| n == "stilt.toml") {
            let text = fs::read_to_string(&path).expect("a manifest is text");
            fs::write(&path, text.replace(REPOS, repos)).expect("the copy is writable");
        }
    }
}

fn stilt(args: &[&str], program: &Path) -> Output {
    let output = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(args)
        .arg(program)
        .env("STILT_HOME", cache(&named(program)))
        .output()
        .expect("the compiler runs");
    common::stop_engine(Path::new("."), program);
    output
}

/// What is wrong with a program and its snapshot.
fn problems(program: &Path) -> Vec<String> {
    let Some(code) = named_code(program) else {
        return vec!["its name doesn't start with a registered code".to_owned()];
    };
    let prepared = prepare(program);
    let checked = &prepared.path;
    if let Some(edits) = edits_of(program) {
        return refusal_problems(program, code, &edits);
    }
    let mut found = Vec::new();
    let json: Value = serde_json::from_slice(&stilt(&["check", "--json"], checked).stdout)
        .expect("`check --json` prints JSON");
    match json["diagnostics"].as_array().map(Vec::as_slice) {
        Some([d]) if d["code"] == code.as_str() => {
            found.extend(record_shape::shape(d));
            found.extend(fixes_work(checked, d));
        }
        Some(all) => {
            let reported: Vec<_> = all.iter().map(|d| d["code"].to_string()).collect();
            found.push(format!(
                "it reports [{}] rather than {code} alone",
                reported.join(", ")
            ));
        }
        None => found.push("`check --json` has no diagnostics".to_owned()),
    }
    let rendered = prepared.shown(&stilt(&["check"], checked).stderr);
    match fs::read(program.with_extension("stderr")) {
        Ok(snapshot) if snapshot == rendered => {}
        Ok(_) => found.push("its rendering differs from its snapshot".to_owned()),
        Err(_) => found.push("it has no snapshot".to_owned()),
    }
    found
}

/// The edits of a refusal's program: the arguments of its `--edit` options, an address and a
/// text for each, as its `edits` file gives them.
fn edits_of(program: &Path) -> Option<Vec<String>> {
    let text = fs::read_to_string(program.with_extension("edits")).ok()?;
    Some(text.lines().map(str::to_owned).collect())
}

/// The arguments of `check` for a command with `edits`.
fn edit_args(edits: &[String]) -> Vec<String> {
    edits
        .chunks(2)
        .flat_map(|pair| ["--edit".to_owned(), pair[0].clone(), pair[1].clone()])
        .collect()
}

/// What is wrong with a refusal's program and its snapshot: its command must be refused with
/// the code of its name, with status 2 and no change to its file, and render as the snapshot.
fn refusal_problems(program: &Path, code: Code, edits: &[String]) -> Vec<String> {
    let args = edit_args(edits);
    let run = |json: bool| {
        let mut all = vec!["check".to_owned()];
        all.extend(json.then(|| "--json".to_owned()));
        all.extend(args.clone());
        let all: Vec<&str> = all.iter().map(String::as_str).collect();
        stilt(&all, program)
    };
    let mut found = Vec::new();
    let before = fs::read(program).ok();
    let output = run(true);
    let json: Value = serde_json::from_slice(&output.stdout).unwrap_or(Value::Null);
    let refused = json["edits"]
        .as_array()
        .map_or(&[][..], Vec::as_slice)
        .iter()
        .any(|e| e["refused"] == code.as_str());
    if !refused || output.status.code() != Some(2) || json.get("diagnostics").is_some() {
        found.push(format!(
            "its command isn't refused with {code} alone: {json}"
        ));
    }
    if fs::read(program).ok() != before {
        found.push("its command changed its file".to_owned());
    }
    let rendered = run(false).stderr;
    match fs::read(program.with_extension("stderr")) {
        Ok(snapshot) if snapshot == rendered => {}
        Ok(_) => found.push("its rendering differs from its snapshot".to_owned()),
        Err(_) => found.push("it has no snapshot".to_owned()),
    }
    found
}

/// What is wrong with the fixes of a program's one diagnostic: each, applied to a copy, must remove
/// it and cause no other, so that the program checks without any (goal working-fixes;
/// edits.fixes-as-edits). A fix with edits is applied through `check --edit`. A fix without,
/// because it changes text outside every part, is applied through the change it shows, which the
/// diagnostic holds as spans of its file.
fn fixes_work(program: &Path, d: &Value) -> Vec<String> {
    let fixes = d["fixes"].as_array().map_or(&[][..], Vec::as_slice);
    let mut found = Vec::new();
    for (i, fix) in fixes.iter().enumerate() {
        let edits = fix["edits"].as_array().map_or(&[][..], Vec::as_slice);
        let copy = copied(program, i + 1);
        let mut args = vec!["check".to_owned(), "--json".to_owned()];
        if edits.is_empty() {
            apply_change(program, &copy, i);
        }
        for e in edits {
            args.push("--edit".to_owned());
            args.push(e["at"].as_str().unwrap_or_default().to_owned());
            args.push(e["new"].as_str().unwrap_or_default().to_owned());
        }
        let args: Vec<&str> = args.iter().map(String::as_str).collect();
        let output = stilt(&args, &copy);
        let json: Value = serde_json::from_slice(&output.stdout).unwrap_or(Value::Null);
        let left: Vec<String> = json["diagnostics"]
            .as_array()
            .map_or(&[][..], Vec::as_slice)
            .iter()
            .map(|d| d["code"].to_string())
            .collect();
        let applied = edits.is_empty()
            || json["edits"]
                .as_array()
                .is_some_and(|e| e.iter().all(|e| e["applied"] == true));
        if !applied || !left.is_empty() {
            found.push(format!(
                "once fix {} is applied, it reports [{}] (applied: {applied})",
                i + 1,
                left.join(", ")
            ));
        }
    }
    found
}

/// Applies fix `n` of the program's one diagnostic to the file it lies in, in `copy`.
fn apply_change(program: &Path, copy: &Path, n: usize) {
    // The program's packages may link C libraries, which the check asks the loader for as the
    // binary does (c.finding-libraries); without the finder each would be E0611.
    stilt_db::install_library_finder(stilt_runtime::c_libraries::finds);
    let db = stilt_db::Database::default();
    let loaded = stilt_db::load(&db, program).expect("the program loads");
    let found = stilt_rc::check_in_parallel(&db, loaded);
    let d = &found[0];
    let text = String::from_utf8_lossy(d.file.bytes(&db)).into_owned();
    let changed = stilt_diag::apply(&text, &d.diagnostic.fixes[n]);
    let target = if copy.is_dir() {
        copy.join(d.file.path(&db))
    } else {
        copy.to_path_buf()
    };
    fs::write(target, changed).expect("the copy is writable");
}

/// A copy of the program in the test's own directory, for fix `n`.
fn copied(program: &Path, n: usize) -> PathBuf {
    let name = program.file_name().expect("a program has a name");
    let copy = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("fix{n}"))
        .join(name);
    let _ = fs::remove_dir_all(&copy);
    copy_all(program, &copy);
    copy
}

/// A copy of a file, or of a directory and everything in it.
fn copy_all(from: &Path, to: &Path) {
    fs::create_dir_all(to.parent().expect("a copy has a directory")).expect("it can be made");
    if from.is_dir() {
        fs::create_dir_all(to).expect("the copy's directory can be made");
        for entry in fs::read_dir(from).expect("the program is readable") {
            let entry = entry.expect("the program is readable").path();
            copy_all(
                &entry,
                &to.join(entry.file_name().expect("an entry has a name")),
            );
        }
    } else {
        fs::copy(from, to).expect("the program can be copied");
    }
}

#[test]
fn every_snapshot_is_current() {
    let failures: Vec<String> = programs()
        .iter()
        .flat_map(|program| {
            let name = program.strip_prefix(root()).unwrap_or(program).display();
            problems(program)
                .into_iter()
                .map(move |problem| format!("{name}: {problem}"))
        })
        .collect();
    assert!(
        failures.is_empty(),
        "\n{}\n\nA changed message needs a review: put its program in \
         tests/diagnostics/_pending/ and run `just snapshots-draft`.\n",
        failures.join("\n")
    );
}

/// Drafts the snapshot of each program in `_pending/` (`just snapshots-draft`): the rendering of
/// `stilt check`, with the edits of a refusal's program, once what it needs is fetched. A draft is
/// reviewed before `just snapshots-accept` moves it up.
#[test]
#[ignore = "it writes the drafts, so only `just snapshots-draft` runs it"]
fn draft() {
    let pending = root().join("_pending");
    for program in programs().iter().filter(|p| p.parent() == Some(&pending)) {
        let prepared = prepare(program);
        let mut args = vec!["check".to_owned()];
        match edits_of(program) {
            Some(edits) => args.extend(edit_args(&edits)),
            None => drop(stilt(&["check", "--json"], &prepared.path)),
        }
        let args: Vec<&str> = args.iter().map(String::as_str).collect();
        let rendered = prepared.shown(&stilt(&args, &prepared.path).stderr);
        fs::write(program.with_extension("stderr"), rendered).expect("the draft can be written");
    }
}

#[test]
fn every_core_code_has_a_snapshot() {
    let named: BTreeSet<Code> = programs().iter().filter_map(|p| named_code(p)).collect();
    let missing: Vec<&str> = codes::ALL
        .iter()
        .filter(|c| PHASES.contains(&c.entry().phase) && !c.entry().retired)
        .filter(|c| c.entry().tier == TIER)
        .filter(|c| !named.contains(c))
        .map(|c| c.as_str())
        .collect();
    assert!(
        missing.is_empty(),
        "codes without a snapshot: {}",
        missing.join(", ")
    );
}
