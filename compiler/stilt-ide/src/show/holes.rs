//! The context of each hole of a part that `show` shows (goal hole-context; Agent syntax,
//! "Typed holes as context"), in the order Hazel measured: the type it expects and the effects
//! it may perform, the definitions of the types they name, the bindings in scope, and the
//! headers of at most 10 functions whose result fits. Each hole of the part's bodies, those of
//! its doc examples included, has a record in the list `holes` of the part's record, and a
//! block after its text.

use std::fmt::Write as _;

use serde_json::{Value, json};
use stilt_db::{Database, Program};
use stilt_diag::LineIndex;
use stilt_types::holes::{Hole, holes};

use super::lookup::Parts;
use super::parts::FileParts;

/// A hole's context, as `show` writes it.
struct Context {
    line: u32,
    col: u32,
    hole: Hole,
    /// The path and the definition of each type it names.
    types: Vec<(String, String)>,
    headers: Vec<String>,
}

/// The holes of part `i` of `of`, in the order they are written, each with its context.
/// A body's start may come before the body's part, so the bodies are those that start in the
/// part's declaration, and the holes those that are in the part.
fn contexts(db: &Database, program: Program, of: &FileParts, i: usize) -> Vec<Context> {
    let extent = of.parts[i].extent.clone();
    let declaration = of.parts[of.parts[i].decl].extent.clone();
    let starts = stilt_hir::body_starts(db, program, of.file);
    let found: Vec<Hole> = (0..)
        .zip(starts.iter())
        .filter(|(_, start)| declaration.contains(&usize::from(**start)))
        .flat_map(|(index, _)| holes(db, program, of.file, index))
        .filter(|h| extent.contains(&usize::from(h.at.start())))
        .collect();
    if found.is_empty() {
        return Vec::new();
    }
    let lines = LineIndex::new(&of.text);
    let mut parts = Parts::new(db, program);
    found
        .into_iter()
        .map(|hole| {
            let at = lines.position(&of.text, hole.at.start());
            let types = hole
                .types
                .iter()
                .filter_map(|t| {
                    let path = format!("{}.{}", t.home, t.name);
                    Some((path.clone(), parts.definition(&path)?))
                })
                .collect();
            let headers = hole.fits.iter().filter_map(|f| parts.header(f)).collect();
            Context {
                line: at.line,
                col: at.col,
                hole,
                types,
                headers,
            }
        })
        .collect()
}

/// The records of the holes of part `i` of `of`, or `None` if it has none.
pub(super) fn json(db: &Database, program: Program, of: &FileParts, i: usize) -> Option<Value> {
    let records: Vec<Value> = contexts(db, program, of, i)
        .into_iter()
        .map(|c| {
            json!({
                "line": c.line,
                "col": c.col,
                "expects": c.hole.expects,
                "effects": c.hole.effects,
                "without": c.hole.without,
                "types": c.types.iter()
                    .map(|(path, text)| json!({"path": path, "text": text}))
                    .collect::<Vec<_>>(),
                "in_scope": c.hole.in_scope.iter()
                    .map(|(name, ty)| json!({"name": &**name, "type": ty}))
                    .collect::<Vec<_>>(),
                "headers": c.headers,
            })
        })
        .collect();
    (!records.is_empty()).then_some(Value::Array(records))
}

/// Adds the list `holes` to `record`, the record of part `i` of `of`, if the part has holes.
pub(super) fn annotate(
    db: &Database,
    program: Program,
    record: &mut Value,
    of: &FileParts,
    i: usize,
) {
    if let Some(holes) = json(db, program, of, i) {
        record["holes"] = holes;
    }
}

/// The blocks of the holes of part `i` of `of` for people, each after a blank line.
pub(super) fn text(db: &Database, program: Program, of: &FileParts, i: usize) -> String {
    let mut out = String::new();
    for c in contexts(db, program, of, i) {
        let _ = writeln!(out, "\nhole at {}:{}:{}", of.file.path(db), c.line, c.col);
        let _ = writeln!(out, "  expects: {}", c.hole.expects);
        let effects = if c.hole.effects.is_empty() {
            "none".to_owned()
        } else {
            c.hole.effects.join(", ")
        };
        let _ = writeln!(out, "  effects: {effects}");
        if !c.hole.without.is_empty() {
            let _ = writeln!(out, "  without: {}", c.hole.without.join(", "));
        }
        section(
            &mut out,
            "types",
            c.types.iter().map(|(_, text)| text.clone()),
        );
        let bound = c.hole.in_scope.iter().map(|(n, t)| format!("{n}: {t}"));
        section(&mut out, "in scope", bound);
        section(&mut out, "fits", c.headers.iter().cloned());
    }
    out
}

/// A titled section of a hole's block, each line indented under its title, or nothing if it
/// has no line.
fn section(out: &mut String, title: &str, lines: impl Iterator<Item = String>) {
    let lines: Vec<String> = lines.collect();
    if lines.is_empty() {
        return;
    }
    let _ = writeln!(out, "  {title}:");
    for line in lines {
        for l in line.lines() {
            let _ = writeln!(out, "    {l}");
        }
    }
}
