//! A function as `stilt show` prints it: its code as written, with its facts written in
//! (Inferred facts, "What is inferred"). The facts follow the signature in brackets, as in
//! `fn totals(orders: List<Order>) -> List<(str, f64)> [panic, alloc]` (facts.visibility), and
//! each line that causes one ends with a comment that says what it does there, as does each call
//! that loses reuse (values.consumed-parameters) and each line that gives a binding a mode other
//! than its default (modes.show). Each `let` and `var` that writes no type has the type that
//! inference gives it written in, as in `let xs: List<i64> = [1, 2]` (types.inferred-per-body). A
//! method shows inside the first line of its impl or trait.

use std::collections::BTreeMap;

use stilt_db::{Database, Program};
use stilt_diag::LineIndex;
use stilt_syntax::ast::{self, AstNode as _};
use stilt_syntax::{SyntaxKind, SyntaxNode, TextSize};

use super::facts::Function;
use super::lines::{Change, written};
use crate::text;

/// The function's code with its facts written in, each line ending with a newline, or `None`
/// when its declaration can't be found in its file's tree, as in a file with a syntax error.
/// With `expanded`, each macro use is replaced by its expansion (macros.showing), and its line
/// says how many lines the expansion takes (macros.showing).
pub(super) fn function(
    db: &Database,
    program: Program,
    f: &Function,
    expanded: bool,
) -> Option<String> {
    let text = text(db, f.file);
    let lines = LineIndex::new(&text);
    let start = stilt_hir::body_starts(db, program, f.file)[f.index as usize];
    let decl = declaration(&stilt_db::parse(db, f.file).syntax(), start)?;
    let range = decl.syntax().text_range();
    let first = lines.position(&text, range.start()).line;
    let last = lines
        .position(&text, last_offset(range.start(), range.end()))
        .line;
    let mut changes = types(f);
    let summary = f.summary();
    if let Some(body) = decl.body().map(|b| b.syntax().text_range().start())
        && !summary.is_empty()
    {
        changes.push(Change {
            start: body,
            end: body,
            text: format!("[{}] ", summary.join(", ")),
        });
    }
    let mut sizes: Vec<(u32, String)> = Vec::new();
    if expanded {
        for (change, size) in super::lines::expansions(db, program, f.file, f.index) {
            if let Some(size) = size {
                sizes.push((lines.position(&text, change.start).line, size));
            }
            changes.push(change);
        }
    }
    let mut notes = notes(f);
    for (line, size) in &sizes {
        notes.entry(*line).or_default().push(size);
    }
    let mut out = String::new();
    let parent = decl
        .syntax()
        .parent()
        .filter(|p| p.kind() != SyntaxKind::SOURCE_FILE);
    if let Some(parent) = &parent {
        let at = lines.position(&text, parent.text_range().start()).line;
        out.push_str(lines.line(&text, at).trim_start());
        out.push('\n');
    }
    out.push_str(&written(&text, &lines, (first, last), changes, &notes));
    if parent.is_some() {
        out.push_str("}\n");
    }
    Some(out)
}

/// The types written in after the patterns that write none.
fn types(f: &Function) -> Vec<Change> {
    f.locals
        .iter()
        .map(|l| Change {
            start: l.end,
            end: l.end,
            text: format!(": {}", l.ty),
        })
        .collect()
}

/// What each line that causes a fact says it does there, each once, in the order of the facts
/// in the bracket: a check that a rule of acceptance proves where a `panic` would have been, with
/// the rule (facts.shown-proofs).
#[must_use]
pub fn notes(f: &Function) -> BTreeMap<u32, Vec<&str>> {
    let mut notes: BTreeMap<u32, Vec<&str>> = BTreeMap::new();
    let proved = f.proved.iter().map(|(c, _, _)| c);
    for c in f
        .consumes
        .iter()
        .chain(&f.lost_reuse)
        .chain(&f.modes.escapes)
        .chain(&f.modes.shared)
        .chain(&f.modes.once)
        .chain(&f.views.causes)
        .chain(&f.views.writes)
        .chain(&f.in_place)
        .chain(&f.panic)
        .chain(&f.overflow)
        .chain(proved)
        .chain(&f.alloc)
        .chain(&f.div)
        .chain(&f.copy)
        .chain(&f.locks)
        .chain(f.capabilities.iter().flatten())
        .chain(&f.atomic)
        .chain(&f.unsafe_blocks)
        .chain(&f.foreign)
    {
        let says = notes.entry(c.line).or_default();
        if !says.contains(&c.says.as_str()) {
            says.push(&c.says);
        }
    }
    notes
}

/// The function whose name starts at `start`, where its body starts.
fn declaration(root: &SyntaxNode, start: TextSize) -> Option<ast::Fn> {
    root.descendants().filter_map(ast::Fn::cast).find(|f| {
        f.name()
            .is_some_and(|n| n.syntax().text_range().start() == start)
    })
}

/// The offset of the last byte of a range, which is on its last line.
fn last_offset(start: TextSize, end: TextSize) -> TextSize {
    if end > start {
        end - TextSize::from(1)
    } else {
        start
    }
}
