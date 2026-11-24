//! Writing new texts into a file (edits.writing).

use stilt_syntax::parse;

use crate::canon::canonical;
use crate::parts::{Part, parts};

/// `text` with the source text of each part in `edits` replaced by its new text, written as
/// `stilt fmt` writes it in the part's place, at the part's indentation, and every byte
/// outside the parts as it was. `module` is the file's module, and `found` the parts of `text`.
///
/// The new text is laid out in place when the file with the edits made parses, by formatting it
/// and taking the formatted parts; otherwise it is laid out alone, at column 0, and indented.
/// The edits address parts that don't overlap, each a declaration or a body.
#[must_use]
pub fn splice(module: &str, text: &str, found: &[Part], edits: &[(usize, &str)]) -> String {
    let written = in_place(module, text, found, edits).unwrap_or_else(|| {
        edits
            .iter()
            .map(|&(i, new)| {
                let canonical = canonical(
                    &Part {
                        broken: false,
                        ..found[i].clone()
                    },
                    new,
                );
                reindent(&canonical, "", &indent(text, found[i].extent.start))
            })
            .collect()
    });
    let mut order: Vec<usize> = (0..edits.len()).collect();
    order.sort_by_key(|&k| std::cmp::Reverse(found[edits[k].0].extent.start));
    let mut out = text.to_owned();
    for k in order {
        out.replace_range(found[edits[k].0].extent.clone(), &written[k]);
    }
    out
}

/// The new text of each edit, as the formatter lays out the file once the edits are made.
fn in_place(
    module: &str,
    text: &str,
    found: &[Part],
    edits: &[(usize, &str)],
) -> Option<Vec<String>> {
    let mut order: Vec<usize> = (0..edits.len()).collect();
    order.sort_by_key(|&k| std::cmp::Reverse(found[edits[k].0].extent.start));
    let mut raw = text.to_owned();
    for &k in &order {
        raw.replace_range(found[edits[k].0].extent.clone(), edits[k].1);
    }
    let made = parts(module, &parse(&raw), &raw);
    if made.len() != found.len() {
        return None;
    }
    let formatted = stilt_fmt::format(raw.as_bytes()).ok()?;
    let laid = parts(module, &parse(&formatted), &formatted);
    if laid.len() != found.len() {
        return None;
    }
    edits
        .iter()
        .map(|&(i, _)| {
            let (from, to) = (&laid[i], &found[i]);
            if (from.kind, from.body) != (to.kind, to.body) {
                return None;
            }
            let written = &formatted[from.extent.clone()];
            Some(reindent(
                written,
                &indent(&formatted, from.extent.start),
                &indent(text, to.extent.start),
            ))
        })
        .collect()
}

/// The indentation of the line that holds the offset `at`.
fn indent(text: &str, at: usize) -> String {
    let start = text[..at].rfind('\n').map_or(0, |i| i + 1);
    text[start..]
        .chars()
        .take_while(|c| matches!(c, ' ' | '\t'))
        .collect()
}

/// A text whose lines after the first are indented by `from`, with `to` in its place.
fn reindent(text: &str, from: &str, to: &str) -> String {
    let mut lines = text.split('\n');
    let mut out = lines.next().unwrap_or_default().to_owned();
    for line in lines {
        out.push('\n');
        if !line.is_empty() {
            out.push_str(to);
            out.push_str(line.strip_prefix(from).unwrap_or(line));
        }
    }
    out
}
