//! The holes suite (goal hole-context). Each hole of each program under `tests/holes/` is
//! marked `//~ HOLE` at the end of its line, and the annotation lines after it give the context
//! that the rules of `show` give it, which `stilt show --json` must show
//! ([its README](../../../tests/holes/README.md)).

mod common;

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use common::suite;
use serde_json::Value;

/// The most functions that a hole's context lists.
const MOST: usize = 10;

/// What the annotations of a hole expect.
#[derive(Debug, Default)]
struct Expected {
    expects: Option<String>,
    effects: Option<String>,
    without: Option<String>,
    types: Vec<String>,
    in_scope: Vec<String>,
    fits: Vec<String>,
    not: Vec<String>,
}

/// A hole, by its file and line.
type At = (String, u32);

/// The holes that a file's annotations expect, with what they expect.
fn expected(path: &Path, file: &str) -> Result<BTreeMap<At, Expected>, String> {
    let text = fs::read_to_string(path).map_err(|e| format!("{file}: {e}"))?;
    let mut holes = BTreeMap::new();
    let mut current: Option<At> = None;
    for (n, line) in (1..).zip(text.lines()) {
        let Some((before, annotation)) = line.split_once("//~") else {
            current = None;
            continue;
        };
        let annotation = annotation.trim();
        if !before.trim().is_empty() {
            if annotation != "HOLE" {
                return Err(format!("{file}:{n}: an unknown annotation `{annotation}`"));
            }
            let at = (file.to_owned(), n);
            holes.insert(at.clone(), Expected::default());
            current = Some(at);
            continue;
        }
        let Some(at) = &current else {
            return Err(format!("{file}:{n}: an annotation that follows no hole"));
        };
        let hole = holes.get_mut(at).expect("the hole is expected");
        let (key, value) = annotation
            .split_once(": ")
            .ok_or(format!("{file}:{n}: an annotation without a key"))?;
        let value = value.trim().to_owned();
        match key {
            "expects" => hole.expects = Some(value),
            "effects" => hole.effects = Some(value),
            "without" => hole.without = Some(value),
            "type" => hole.types.push(value),
            "in scope" => hole.in_scope.push(value),
            "fits" => hole.fits.push(value),
            "not" => hole.not.push(value),
            _ => return Err(format!("{file}:{n}: an unknown key `{key}`")),
        }
    }
    Ok(holes)
}

/// The holes that `stilt show --json` gives a module of the program, by file and line.
fn shown(program: &Path, module: &str) -> Result<BTreeMap<At, Value>, String> {
    let record = suite::show_module(program, module)?;
    let mut holes = BTreeMap::new();
    let records = record["functions"]
        .as_array()
        .into_iter()
        .chain(record["declarations"].as_array())
        .flatten();
    for r in records {
        let file = r["file"].as_str().unwrap_or_default().to_owned();
        for h in r["holes"].as_array().into_iter().flatten() {
            let line = u32::try_from(h["line"].as_u64().unwrap_or(0)).unwrap_or(0);
            holes.insert((file.clone(), line), h.clone());
        }
    }
    Ok(holes)
}

fn strings(v: &Value) -> Vec<String> {
    v.as_array()
        .into_iter()
        .flatten()
        .map(|s| s.as_str().unwrap_or_default().to_owned())
        .collect()
}

/// A list as an annotation writes it: its elements joined by `, `, or `none`.
fn joined(v: &Value) -> String {
    let all = strings(v);
    if all.is_empty() {
        "none".to_owned()
    } else {
        all.join(", ")
    }
}

/// The types a hole's context defines, each with its whitespace runs as single spaces, and its
/// bindings in scope, as the annotations write them.
fn listed(shown: &Value) -> (Vec<String>, Vec<String>) {
    let all = |key: &str| shown[key].as_array().into_iter().flatten();
    let types = all("types")
        .map(|t| {
            let text = t["text"].as_str().unwrap_or_default();
            text.split_whitespace().collect::<Vec<_>>().join(" ")
        })
        .collect();
    let in_scope = all("in_scope")
        .map(|b| {
            let name = b["name"].as_str().unwrap_or_default();
            format!("{name}: {}", b["type"].as_str().unwrap_or_default())
        })
        .collect();
    (types, in_scope)
}

/// What differs between a hole's expected and shown context.
fn differences(at: &At, expected: &Expected, shown: &Value) -> Vec<String> {
    let place = format!("{}:{}", at.0, at.1);
    let mut problems = Vec::new();
    let mut same = |what: &str, want: Option<&String>, got: String| match want {
        Some(want) if *want == got => {}
        Some(want) => problems.push(format!("{place}: {what} is `{got}`, not `{want}`")),
        None => problems.push(format!("{place}: no `{what}` annotation; it is `{got}`")),
    };
    let expects = shown["expects"].as_str().unwrap_or_default().to_owned();
    same("expects", expected.expects.as_ref(), expects);
    same(
        "effects",
        expected.effects.as_ref(),
        joined(&shown["effects"]),
    );
    let without = expected
        .without
        .clone()
        .unwrap_or_else(|| "none".to_owned());
    same("without", Some(&without), joined(&shown["without"]));
    let (types, in_scope) = listed(shown);
    if types != expected.types {
        let want = &expected.types;
        problems.push(format!("{place}: the types are {types:?}, not {want:?}"));
    }
    if in_scope != expected.in_scope {
        let want = &expected.in_scope;
        problems.push(format!("{place}: in scope are {in_scope:?}, not {want:?}"));
    }
    let headers = strings(&shown["headers"]);
    problems.extend(fit_differences(&place, expected, &headers));
    problems
}

/// Whether the headers that fit hold those expected, in their order, and none of those
/// expected not to, and at most [`MOST`].
fn fit_differences(place: &str, expected: &Expected, headers: &[String]) -> Vec<String> {
    let mut problems = Vec::new();
    if headers.len() > MOST {
        problems.push(format!("{place}: {} headers, over {MOST}", headers.len()));
    }
    let mut rest = headers.iter();
    for want in &expected.fits {
        if !rest.any(|h| h == want) {
            problems.push(format!(
                "{place}: `{want}` doesn't fit in its order; the headers are {headers:?}"
            ));
        }
    }
    for unwanted in &expected.not {
        if headers.contains(unwanted) {
            problems.push(format!("{place}: `{unwanted}` fits, but shouldn't"));
        }
    }
    problems
}

/// What differs between a module's expected and shown holes, if anything does.
fn compare(program: &Path, module: &str, file: &str) -> Result<(), String> {
    let expected = expected(&suite::source(program, file), file)?;
    let shown = shown(program, module)?;
    let mut problems = Vec::new();
    for (at, want) in &expected {
        match shown.get(at) {
            Some(got) => problems.extend(differences(at, want, got)),
            None => problems.push(format!("{}:{}: a hole expected, none shown", at.0, at.1)),
        }
    }
    for at in shown.keys().filter(|at| !expected.contains_key(*at)) {
        problems.push(format!("{}:{}: a hole shown, none expected", at.0, at.1));
    }
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}

#[test]
fn every_hole_shows_the_context_the_rules_give() {
    let programs = suite::programs(&suite::root("holes"));
    assert!(!programs.is_empty(), "the suite has programs");
    let failures: Vec<String> = programs
        .iter()
        .flat_map(|p| {
            suite::modules(p)
                .into_iter()
                .map(move |(module, file)| (p, module, file))
        })
        .filter_map(|(program, module, file)| compare(program, &module, &file).err())
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
