//! The shape that `check --json` gives each diagnostic, which the snapshots check: a message, a
//! title and a help, one primary span, at most two fixes that are edits, the admissible
//! alternatives (goal admissible-alternatives) and a mismatch's chain (goal one-form-per-reader).

use serde_json::Value;
use stilt_diag::{MAX_ALTERNATIVES, MAX_FIXES};

/// What a diagnostic lacks of the shape one-diagnostic-shape asks for: a message, a title, a
/// help, one primary span among its labels, and at most two fixes, each with a title and the edits of
/// edits.json-form, which may be none; and a list of at most 10 admissible alternatives, each with
/// a kind and a text, and a type for a binding (admissible-alternatives).
pub(crate) fn shape(d: &Value) -> Vec<String> {
    let text = |v: &Value| v.as_str().is_some_and(|s| !s.is_empty());
    let mut found = Vec::new();
    if !text(&d["message"]) || !text(&d["title"]) || !text(&d["help"]) {
        found.push("it has no message, no title or no help".to_owned());
    }
    let labels = d["labels"].as_array().map_or(&[][..], Vec::as_slice);
    if labels.iter().filter(|l| l["primary"] == true).count() != 1 {
        found.push("it has no primary span, or more than one".to_owned());
    }
    let fixes = d["fixes"].as_array().map_or(&[][..], Vec::as_slice);
    if fixes.len() > MAX_FIXES {
        found.push(format!("it offers more than {MAX_FIXES} fixes"));
    }
    let edit = |e: &Value| text(&e["at"]) && e["new"].is_string();
    if fixes.iter().any(|f| {
        !text(&f["title"])
            || f["edits"]
                .as_array()
                .is_none_or(|edits| !edits.iter().all(edit))
    }) {
        found.push("a fix has no title, or an edit that isn't {at, new}".to_owned());
    }
    found.extend(alternatives_shape(d));
    found.extend(chain_shape(d));
    found
}

/// What a mismatch's `chain` lacks of the shape one-form-per-reader asks for: each type mismatch
/// has one, and each of its steps is a span and what it gave, the last at the mismatch.
fn chain_shape(d: &Value) -> Vec<String> {
    let mismatch = d["code"] == "E0311"
        && d["message"]
            .as_str()
            .is_some_and(|m| m.starts_with("expected `"));
    let Some(steps) = d["chain"].as_array() else {
        return if mismatch {
            vec!["its mismatch has no chain".to_owned()]
        } else {
            Vec::new()
        };
    };
    let span = |v: &Value| {
        v.as_array().is_some_and(|ends| {
            ends.len() == 2
                && ends
                    .iter()
                    .all(|e| e.as_array().is_some_and(|p| p.len() == 2))
        })
    };
    let mut found = Vec::new();
    if steps
        .iter()
        .any(|s| !span(&s["range"]) || s["text"].as_str().is_none_or(str::is_empty))
    {
        found.push("a step of its chain has no span or no text".to_owned());
    }
    let primary = d["labels"]
        .as_array()
        .and_then(|ls| ls.iter().find(|l| l["primary"] == true));
    if steps.last().map(|s| &s["range"]) != primary.map(|l| &l["range"]) {
        found.push("its chain doesn't end where it points".to_owned());
    }
    found
}

/// What a diagnostic's list `alternatives` lacks of the shape admissible-alternatives asks for.
fn alternatives_shape(d: &Value) -> Vec<String> {
    const KINDS: [&str; 6] = ["binding", "variant", "effect", "method", "field", "name"];
    let Some(alternatives) = d["alternatives"].as_array() else {
        return vec!["it has no list of alternatives".to_owned()];
    };
    let mut found = Vec::new();
    if alternatives.len() > MAX_ALTERNATIVES {
        found.push(format!(
            "it lists more than {MAX_ALTERNATIVES} alternatives"
        ));
    }
    for a in alternatives {
        let kind = a["kind"].as_str().unwrap_or_default();
        let typed = a.get("type").is_some_and(Value::is_string);
        if !KINDS.contains(&kind) || a["text"].as_str().is_none_or(str::is_empty) {
            found.push(format!("an alternative without a kind or a text: {a}"));
        } else if typed != (kind == "binding") {
            found.push(format!(
                "an alternative whose type doesn't go with its kind: {a}"
            ));
        }
    }
    found
}
