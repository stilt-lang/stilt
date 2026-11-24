//! A fix as edits of parts (edits.fixes-as-edits).

use std::ops::Range;

use crate::canon::{canonical, hash};
use crate::parts::Part;

/// A change that a fix makes to a file: the text that replaces a span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Replacement {
    /// The bytes of the file that the fix replaces.
    pub range: Range<usize>,
    /// The text written in their place.
    pub text: String,
}

/// An edit of a part, in its JSON form (edits.json-form): the part's address with its current hash,
/// and the part's whole new text in canonical format.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixEdit {
    /// The address of the part, with its current hash.
    pub at: String,
    /// The part's whole new text.
    pub new: String,
}

/// The edits that make the `changes` of a fix to the file `text`, one for each declaration it
/// changes, whose parts are `found`. An edit addresses the declaration's body when every change
/// in the declaration lies in the body, and the declaration otherwise. A fix that changes text
/// outside every declaration, or a declaration whose path names two parts (`ambiguous`), has no
/// edits.
#[must_use]
pub fn fix_edits(
    text: &str,
    found: &[Part],
    ambiguous: impl Fn(&str) -> bool,
    changes: &[Replacement],
) -> Vec<FixEdit> {
    let mut groups: Vec<(usize, Vec<&Replacement>)> = Vec::new();
    for change in changes {
        let Some(decl) = innermost(found, &change.range) else {
            return Vec::new();
        };
        match groups.iter_mut().find(|(d, _)| *d == decl) {
            Some((_, group)) => group.push(change),
            None => groups.push((decl, vec![change])),
        }
    }
    // A change in a declaration that another declaration holds, as a trait holds its methods,
    // is a change of the outer one, so that no two edits overlap.
    let held = |inner: usize, outer: usize| {
        inner != outer && contains(&found[outer].extent, &found[inner].extent)
    };
    let outer: Vec<usize> = groups.iter().map(|&(d, _)| d).collect();
    let mut merged: Vec<(usize, Vec<&Replacement>)> = Vec::new();
    for (d, group) in groups {
        let d = outer.iter().copied().find(|&o| held(d, o)).unwrap_or(d);
        match merged.iter_mut().find(|(m, _)| *m == d) {
            Some((_, all)) => all.extend(group),
            None => merged.push((d, group)),
        }
    }
    let mut edits = Vec::new();
    for (decl, group) in merged {
        if ambiguous(&found[decl].path) {
            return Vec::new();
        }
        edits.push(edit(text, found, decl, &group));
    }
    edits
}

/// The declaration with the smallest extent that holds `range`.
fn innermost(found: &[Part], range: &Range<usize>) -> Option<usize> {
    (0..found.len())
        .filter(|&i| !found[i].body && contains(&found[i].extent, range))
        .min_by_key(|&i| found[i].extent.len())
}

fn contains(outer: &Range<usize>, inner: &Range<usize>) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}

/// The edit of the declaration `decl` that makes `group`.
fn edit(text: &str, found: &[Part], decl: usize, group: &[&Replacement]) -> FixEdit {
    let body = found
        .iter()
        .find(|p| p.body && p.decl == decl)
        .filter(|b| group.iter().all(|c| contains(&b.extent, &c.range)));
    let part = body.unwrap_or(&found[decl]);
    let source = &text[part.extent.clone()];
    let mut changed = source.to_owned();
    let mut ordered: Vec<&&Replacement> = group.iter().collect();
    ordered.sort_by_key(|c| std::cmp::Reverse(c.range.start));
    for c in ordered {
        let range = c.range.start - part.extent.start..c.range.end - part.extent.start;
        changed.replace_range(range, &c.text);
    }
    FixEdit {
        at: format!("{}#{}", part.address(), hash(&canonical(part, source))),
        new: canonical(
            &Part {
                broken: false,
                ..part.clone()
            },
            &changed,
        ),
    }
}
