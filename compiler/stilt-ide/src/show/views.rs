//! The views of a function as `show` prints them (views.show; projections.show): `` `w`
//! views `text` `` at the line of each binding of a view type, naming each source it reads, ``
//! `tail` writes `xs` `` at the line of a writable binding, naming each source it writes, and
//! ``the result views `line` `` or ``the result writes `xs` `` at the line of each expression
//! returned that views the parameter `line` or writes the `inout` parameter `xs`, which the
//! bracket after the signature names as `views line` or `writes xs`. Each word stands for
//! `fixed`, which every view is (views.fixed), so no view prints `fixed`.

use stilt_hir::hir::Name;

use stilt_db::{Database, Program, SourceFile};
use stilt_diag::LineIndex;

use super::facts::{Cause, distinct};
use crate::text;

/// The views of a function, each at its line with the source it reads, or writes, and the
/// parameters its result views or writes, which the bracket names.
#[derive(Clone, Debug, Default)]
pub struct Views {
    pub causes: Vec<Cause>,
    pub writes: Vec<Cause>,
    pub params: Vec<Name>,
    pub written: Vec<Name>,
}

/// The views of the body `index` of `file`, as `show` prints them.
pub(super) fn shown(db: &Database, program: Program, file: SourceFile, index: u32) -> Views {
    let text = text(db, file);
    let lines = LineIndex::new(&text);
    let mut views = Views::default();
    let mut causes = Vec::new();
    let mut writes = Vec::new();
    for v in stilt_types::facts::views(db, program, file, index) {
        let line = lines.position(&text, v.at.start()).line;
        let named: Vec<String> = v.sources.iter().map(|s| format!("`{s}`")).collect();
        let verb = if v.writes { "writes" } else { "views" };
        let says = match &v.binding {
            Some(b) => format!("`{b}` {verb} {}", named.join(" and ")),
            None => format!("the result {verb} {}", named.join(" and ")),
        };
        let (params, found) = if v.writes {
            (&mut views.written, &mut writes)
        } else {
            (&mut views.params, &mut causes)
        };
        for s in &v.sources {
            if v.binding.is_none() && !params.contains(s) {
                params.push(*s);
            }
            found.push(Cause {
                line,
                name: Some(*s),
                says: says.clone(),
            });
        }
    }
    views.causes = distinct(causes.into_iter());
    views.writes = distinct(writes.into_iter());
    views
}
