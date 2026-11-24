//! The lines of a function as `stilt show` prints them: its source lines with text written in
//! at places, as the types inference gives its variables, and with `--expanded` each macro use
//! replaced by its expansion (macros.showing) and the lines it takes reported (macros.showing, rule
//! 16), each line then followed by what its facts say.

use std::collections::BTreeMap;

use stilt_db::{Database, Program, SourceFile};
use stilt_diag::LineIndex;
use stilt_hir::hir::{expanded_source, expanded_text};
use stilt_syntax::TextSize;
use stilt_syntax::forms::Form;

/// A change to the source text: `text` in place of the span from `start` to `end`, which is
/// empty for text written in.
pub(super) struct Change {
    pub(super) start: TextSize,
    pub(super) end: TextSize,
    pub(super) text: String,
}

/// The expansion of each use that the code of a body's user wrote, in place of the use, with
/// the lines the expansion takes in the canonical format, which `show` reports for the use
/// (macros.showing; visible-expansion-size), when the formatter writes it.
pub(super) fn expansions(
    db: &Database,
    program: Program,
    file: SourceFile,
    index: u32,
) -> Vec<(Change, Option<String>)> {
    let body = stilt_hir::module_body(db, program, file, index);
    let start = stilt_hir::body_starts(db, program, file)[index as usize];
    (0..body.expansions.len())
        .filter(|&i| body.expansions[i].parent.is_none())
        .map(|i| {
            let e = &body.expansions[i];
            let at = e.at + start;
            let change = Change {
                start: at.start(),
                end: at.end(),
                text: expanded_text(&body.expansions, i),
            };
            let size = size(e.form, &expanded_source(&body.expansions, i)).map(|n| {
                let lines = if n == 1 { "line" } else { "lines" };
                format!("`{}!` expands to {n} {lines}", e.name)
            });
            (change, size)
        })
        .collect()
}

/// How many lines the canonical format writes code of `form` in: the lines it takes in a
/// function's body, as a statement, the pattern of an arm or the type of a binding, without
/// those that hold it there, or one when the formatter writes all of them on one line.
fn size(form: Form, code: &str) -> Option<usize> {
    let (before, after, held) = match form {
        Form::Expr | Form::Block => ("fn f() {\n", "\n}\n", 2),
        Form::Pattern => ("fn f() {\n  match x {\n    ", " => ()\n  }\n}\n", 4),
        Form::Type => ("fn f() {\n  let x: ", " = y\n}\n", 2),
    };
    let formatted = stilt_fmt::format(format!("{before}{code}{after}").as_bytes()).ok()?;
    Some(formatted.lines().count().saturating_sub(held).max(1))
}

/// The lines `first` to `last` of `text` with `changes` made, each followed by ` // ` and what
/// `notes` say of it, and of the lines a change folded into it, and by a newline.
pub(super) fn written(
    text: &str,
    lines: &LineIndex,
    (first, last): (u32, u32),
    mut changes: Vec<Change>,
    notes: &BTreeMap<u32, Vec<&str>>,
) -> String {
    // Of two changes at one place, the later is written first.
    let mut order: Vec<usize> = (0..changes.len()).collect();
    order.sort_by_key(|&i| (changes[i].start, std::cmp::Reverse(i)));
    let mut sorted: Vec<Change> = Vec::with_capacity(changes.len());
    let mut taken: Vec<Option<Change>> = changes.drain(..).map(Some).collect();
    sorted.extend(order.into_iter().filter_map(|i| taken[i].take()));
    let mut next = sorted.into_iter().peekable();
    let mut out = String::new();
    let mut line = String::new();
    let mut says: Vec<&str> = Vec::new();
    let mut pos = lines.line_start(text, first);
    for n in first..=last {
        let start = lines.line_start(text, n);
        let end = start + TextSize::of(lines.line(text, n));
        for s in notes.get(&n).into_iter().flatten() {
            if !says.contains(s) {
                says.push(s);
            }
        }
        if pos > end {
            continue;
        }
        pos = pos.max(start);
        while let Some(change) = next.next_if(|c| c.start >= pos && c.start <= end) {
            line.push_str(&text[usize::from(pos)..usize::from(change.start)]);
            pos = change.end.max(change.start);
            // An expansion that is a block, in an interpolation, keeps a space from its braces,
            // which would read as one escaped.
            let after = text[usize::from(pos)..].starts_with('}') && change.text.ends_with('}');
            if line.ends_with('{') && change.text.starts_with('{') {
                line.push(' ');
            }
            line.push_str(&change.text);
            if after {
                line.push(' ');
            }
        }
        if pos > end {
            continue;
        }
        line.push_str(&text[usize::from(pos)..usize::from(end)]);
        pos = end + TextSize::from(1);
        if !says.is_empty() {
            line.push_str(" // ");
            line.push_str(&says.join("; "));
        }
        out.push_str(&line);
        out.push('\n');
        line.clear();
        says.clear();
    }
    out
}
