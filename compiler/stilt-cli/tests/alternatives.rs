//! The alternatives suite (goal admissible-alternatives). Each diagnostic of each program under
//! `tests/alternatives/` is marked `//~ CODE` at the end of its line, and the annotation lines
//! after it give the admissible alternatives that the rules give it, which `stilt check
//! --json` must list ([its README](../../../tests/alternatives/README.md)).

mod common;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use common::suite;
use serde_json::Value;

/// A diagnostic, by its file, line and code.
type At = (String, u32, String);

/// The diagnostics that a file's annotations expect, each with its alternatives as
/// `KIND TEXT`, and `KIND name: Type` for a binding.
fn expected(path: &Path, file: &str) -> Result<BTreeMap<At, Vec<String>>, String> {
    let text = fs::read_to_string(path).map_err(|e| format!("{file}: {e}"))?;
    let mut found = BTreeMap::new();
    let mut current: Option<At> = None;
    for (n, line) in (1..).zip(text.lines()) {
        let Some((before, annotation)) = line.split_once("//~") else {
            current = None;
            continue;
        };
        let annotation = annotation.trim();
        if !before.trim().is_empty() {
            let code = annotation.to_owned();
            if code.len() != 5 || !code.starts_with(['E', 'W']) {
                return Err(format!("{file}:{n}: an unknown annotation `{annotation}`"));
            }
            let at = (file.to_owned(), n, code);
            found.insert(at.clone(), Vec::new());
            current = Some(at);
            continue;
        }
        let (Some(at), Some(alternative)) = (&current, annotation.strip_prefix("alternative: "))
        else {
            return Err(format!(
                "{file}:{n}: an annotation that follows no diagnostic"
            ));
        };
        found
            .get_mut(at)
            .expect("the diagnostic is expected")
            .push(alternative.trim().to_owned());
    }
    Ok(found)
}

/// The diagnostics that `stilt check --json` gives the program, each with its alternatives
/// as the annotations write them.
fn shown(program: &Path) -> Result<BTreeMap<At, Vec<String>>, String> {
    let (dir, path) = if program.is_dir() {
        (program.to_path_buf(), PathBuf::from("."))
    } else {
        let dir = program.parent().expect("a file has a directory");
        let name = program.file_name().expect("a file has a name");
        (dir.to_path_buf(), PathBuf::from(name))
    };
    let output = Command::new(env!("CARGO_BIN_EXE_stilt"))
        .args(["check", "--json"])
        .arg(&path)
        .current_dir(&dir)
        .output()
        .expect("stilt runs");
    common::stop_engine(&dir, &path);
    let record: Value = serde_json::from_slice(&output.stdout).map_err(|e| e.to_string())?;
    let mut found = BTreeMap::new();
    for d in record["diagnostics"].as_array().into_iter().flatten() {
        let at = (
            d["file"].as_str().unwrap_or_default().to_owned(),
            u32::try_from(d["line"].as_u64().unwrap_or(0)).unwrap_or(0),
            d["code"].as_str().unwrap_or_default().to_owned(),
        );
        let alternatives = d["alternatives"]
            .as_array()
            .into_iter()
            .flatten()
            .map(written)
            .collect();
        found.insert(at, alternatives);
    }
    Ok(found)
}

/// An alternative as an annotation writes it.
fn written(a: &Value) -> String {
    let text = a["text"].as_str().unwrap_or_default();
    let kind = a["kind"].as_str().unwrap_or_default();
    match a["type"].as_str() {
        Some(ty) => format!("{kind} {text}: {ty}"),
        None => format!("{kind} {text}"),
    }
}

/// What differs between a program's expected and shown diagnostics, if anything does.
fn compare(program: &Path) -> Result<(), String> {
    let mut expected_all = BTreeMap::new();
    for (_, file) in suite::modules(program) {
        expected_all.extend(expected(&suite::source(program, &file), &file)?);
    }
    let shown = shown(program)?;
    let mut problems = Vec::new();
    for (at, want) in &expected_all {
        let place = format!("{}:{} {}", at.0, at.1, at.2);
        match shown.get(at) {
            Some(got) if got == want => {}
            Some(got) => problems.push(format!("{place}: lists {got:?}, not {want:?}")),
            None => problems.push(format!("{place}: expected, not reported")),
        }
    }
    for at in shown.keys().filter(|at| !expected_all.contains_key(*at)) {
        problems.push(format!(
            "{}:{} {}: reported, not expected",
            at.0, at.1, at.2
        ));
    }
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}

#[test]
fn every_diagnostic_lists_the_alternatives_the_rules_give() {
    let programs = suite::programs(&suite::root("alternatives"));
    assert!(!programs.is_empty(), "the suite has programs");
    let failures: Vec<String> = programs.iter().filter_map(|p| compare(p).err()).collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
