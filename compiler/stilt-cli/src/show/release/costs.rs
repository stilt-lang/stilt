//! What a function's release code still costs (builds.performance-report): the reference-count
//! operations that its code performs, its closures' among it, a release that may keep its value's
//! memory among them, and the copies among them, each a count's increment (modes.copies and modes.shared-writes); and the checks of its body that
//! verification proves and the release build drops, and those it keeps (facts.proved-indexes,
//! facts.proved-divisions, facts.map-keys, facts.proved-overflow, facts.range-loops, facts.guards,
//! facts.divisors and facts.keys; builds.dropped-checks), each at its line.
//!
//! An operation is at the line of its location when that is in the function's declaration, and
//! otherwise, as for the code of a function inlined into it, at the line of the last location
//! of the function before it, from its name's line on.

use stilt_db::{Database, Program};
use stilt_diag::LineIndex;
use stilt_mir::mir::{Function, PROVED_CHECK, PROVED_OVERFLOW, Runtime, Rvalue, Stmt, line_of};
use stilt_types::verify::Check as Ruled;

use stilt_ide::show::facts::Function as Declared;

/// A check, by its kind, as a panic names it (effects.panic-kinds), and its line.
pub(crate) type Check = (&'static str, u32);

/// The costs of the code compiled for a function.
#[derive(Debug, Default)]
pub(crate) struct Costs {
    /// Each reference-count operation, by its line, and whether it is a copy.
    pub(crate) references: Vec<(u32, bool)>,
    /// The checks that the code performs.
    pub(crate) kept: Vec<Check>,
    /// The checks that verification proved, which the code drops.
    pub(crate) proved: Vec<Check>,
}

/// Where a function's declaration is: its file's index among the program's, the lines it
/// spans, and its name's line.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Scope {
    pub(crate) file: u64,
    pub(crate) lines: (u32, u32),
    pub(crate) named: u32,
}

impl Scope {
    /// The line of a location word, if it is in the declaration.
    fn line(self, word: u64) -> Option<u32> {
        let word = word & !(PROVED_CHECK | PROVED_OVERFLOW);
        let line = line_of(word);
        let file = word >> 44 & 0xffff;
        (file == self.file && self.lines.0 <= line && line <= self.lines.1).then_some(line)
    }
}

/// The reference-count operations of the functions compiled for a function, its closures'
/// among them, in the order of their lines.
pub(crate) fn references<'f>(
    functions: impl IntoIterator<Item = &'f Function>,
    scope: Scope,
) -> Vec<(u32, bool)> {
    let mut out = Vec::new();
    for f in functions {
        let mut line = scope.named;
        for s in f.blocks.iter().flat_map(|b| &b.stmts) {
            match s {
                Stmt::At(word) => line = scope.line(*word).unwrap_or(line),
                Stmt::Dup(l) | Stmt::Drop(l) if f.locals[l.0 as usize].repr.counted() => {
                    out.push((line, matches!(s, Stmt::Dup(_))));
                }
                // A release that may keep the value's memory for an object built in its place.
                Stmt::Assign(_, Rvalue::Runtime(Runtime::Reclaim, _)) => out.push((line, false)),
                _ => {}
            }
        }
    }
    out.sort_unstable();
    out
}

/// The checks of the body of `f` that the analysis or a rule of acceptance proves, which a
/// release build drops, and those neither does, which the build keeps, each kind at a line once
///.
pub(crate) fn checks(db: &Database, program: Program, f: &Declared) -> (Vec<Check>, Vec<Check>) {
    let proofs = stilt_types::released(db, program, f.file, f.index);
    let text = crate::report::text(db, f.file);
    let lines = LineIndex::new(&text);
    let start = stilt_hir::body_starts(db, program, f.file)[f.index as usize];
    let line = |at: stilt_syntax::TextRange| lines.position(&text, start + at.start()).line;
    let mut proved: Vec<Check> = (proofs.proved.iter())
        .filter(|p| proofs.proves(p.at, p.check))
        .map(|p| (kind(p.check), line(p.at)))
        .collect();
    let mut kept: Vec<Check> = (proofs.unproved.iter())
        .map(|(at, check)| (kind(*check), line(*at)))
        .collect();
    for checks in [&mut proved, &mut kept] {
        checks.sort_unstable_by_key(|&(kind, line)| (line, kind));
        checks.dedup();
    }
    (proved, kept)
}

/// The kind of panic that a check rules out, as a panic names it.
fn kind(check: Ruled) -> &'static str {
    check.shown().unwrap_or("overflow")
}
