//! The reads that views make (views.reads-that-last and views.change-while-viewed), and the writes
//! of writable bindings (projections.what-view-writes): a binding of a view type reads each of its
//! sources for its scope, as `for p in e` reads `e` for its body, and a writable binding writes
//! each source its view writes for its scope; a view that no binding holds reads its sources until
//! the end of the statement that holds it, which for a `for` over a view is the loop's body, and
//! for a view argument covers the call. A modification of a place that overlaps a source while a
//! view reads it is E0423, and any access to one while a writable binding writes it is E0429, at
//! the access, naming the view and where its read or write ends, with a note there, and counted as
//! E0404 is: once, however many reads it conflicts with (modes.change-while-iterating).

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_hir::hir::{LocalId, Name};
use stilt_syntax::{TextRange, TextSize};

use super::places::{Aliases, Place, overlap};
use crate::analyses::views::Sources;
use crate::analyses::views::sources::bound_by;
use crate::tast::walk;
use crate::tast::{Block, Expr, ExprKind, Stmt, StmtKind};

/// The view that reads a source.
#[derive(Clone, Debug)]
pub(super) enum Reader<'a> {
    /// A binding, by its variable, in the statement `index` of `block`.
    Bound {
        var: LocalId,
        block: &'a Block,
        index: usize,
    },
    /// A view that no binding holds.
    Unbound,
}

/// A read of a source that a view makes, or a write of one that a writable binding makes
/// (projections.what-view-writes), which lasts until `ends`.
#[derive(Clone, Debug)]
pub(super) struct Read<'a> {
    pub(super) source: Place,
    pub(super) reader: Reader<'a>,
    pub(super) ends: TextSize,
    /// Whether a writable binding writes the place, which no access may reach.
    pub(super) writes: bool,
}

/// The reads in progress, innermost last.
pub(super) struct Viewing<'a> {
    pub(super) sources: &'a Sources,
    /// The names of `when`s that count as one (shared.names-that-may-be-one-place).
    pub(super) aliases: Aliases,
    pub(super) reads: Vec<Read<'a>>,
    /// The body's text from its start, which fixes are written from, read only for one.
    pub(super) text: &'a dyn Fn() -> Option<String>,
}

impl<'a> Viewing<'a> {
    /// Starts the reads of a view that no binding holds, made by `e`, until `ends`.
    pub(super) fn unbound(&mut self, e: &Expr, ends: TextSize) {
        if matches!(e.kind, ExprKind::Local(_)) || !(e.ty.is_view() || is_closure(e)) {
            return;
        }
        for source in self.sources.places(e) {
            self.reads.push(Read {
                source,
                reader: Reader::Unbound,
                ends,
                writes: false,
            });
        }
    }

    /// Starts the reads of the sources that the argument `index` of the call `e`, just evaluated,
    /// gives the view that `e` returns, until `ends`, so that a later argument may not change them
    /// (views.reads-that-last). They come after the reads in progress, so that a change that one
    /// of those meets names it.
    pub(super) fn operand(&mut self, e: &Expr, index: usize, ends: TextSize) {
        for source in self.sources.operand(e, index) {
            self.reads.push(Read {
                source,
                reader: Reader::Unbound,
                ends,
                writes: false,
            });
        }
    }

    /// Starts the reads of the bindings of view types that the statement `index` of `block` makes,
    /// until `ends`, and the writes of a writable binding among them
    /// (projections.what-view-writes).
    pub(super) fn bound(&mut self, block: &'a Block, index: usize, ends: TextSize) {
        let (StmtKind::Let(b) | StmtKind::Var(b)) = &block[index].kind else {
            return;
        };
        let mut vars: Vec<LocalId> = Vec::new();
        bound_by(&b.pattern, &mut vars);
        for var in vars {
            let writable = self.sources.is_writable(var);
            for source in self.sources.of_binding(var).unwrap_or_default() {
                let Some(place) = source.place() else {
                    continue;
                };
                self.reads.push(Read {
                    source: place.clone(),
                    reader: Reader::Bound { var, block, index },
                    ends,
                    writes: writable && !source.reads(),
                });
            }
        }
    }

    /// E0429 for an access at `at` of the place `p`, if a writable binding writes a source it
    /// overlaps (projections.what-view-writes), and otherwise, when the access is a modification,
    /// `writing`, E0423 if a view reads one (views.change-while-viewed). A write comes first, since
    /// a writable binding's own views read it.
    pub(super) fn conflict(
        &self,
        p: &Place,
        at: TextRange,
        writing: bool,
        locals: &[Name],
    ) -> Option<Diagnostic> {
        let hits = |r: &&Read<'_>| overlap(&r.source, p, &self.aliases);
        let read = match self.reads.iter().filter(|r| r.writes).find(hits) {
            Some(write) => write,
            None if writing => self.reads.iter().find(hits)?,
            None => return None,
        };
        let changed = p.name(locals);
        let source = read.source.name(locals);
        let who = match &read.reader {
            Reader::Bound { var, .. } => format!("`{}`", locals[var.0 as usize]),
            Reader::Unbound => "a view".to_owned(),
        };
        let end = TextRange::new(read.ends - TextSize::from(1), read.ends);
        let d = if read.writes {
            let message = format!("`{changed}` is reached here while {who} writes `{source}`");
            let note = format!("{who} writes `{source}` until here");
            Diagnostic::new(codes::E0429, at, message).with_note(end, note)
        } else {
            let message = format!("`{changed}` changes here while {who} reads `{source}`");
            let note = format!("{who} reads `{source}` until here");
            Diagnostic::new(codes::E0423, at, message).with_note(end, note)
        };
        Some(match read.reader {
            Reader::Bound { block, index, .. } => self.fixes(d, block, index, at, read.writes),
            Reader::Unbound => d,
        })
    }

    /// The fixes of modes.change-while-iterating, and of projections.reaching-written-source for an
    /// access that `reaches` what a writable binding writes, for a change at `at` in a statement of
    /// `block` after the statement `index`, which binds the view: make the change before the view,
    /// by moving the statement that holds it before the binding, and end the view's binding's scope
    /// first, by putting the statements from the binding up to that one in a block. Each is offered
    /// only when the statements it moves past the others don't use what those bind.
    fn fixes(
        &self,
        d: Diagnostic,
        block: &Block,
        index: usize,
        at: TextRange,
        reaches: bool,
    ) -> Diagnostic {
        let Some(change) = block.iter().position(|s| s.at.contains_range(at)) else {
            return d;
        };
        if change <= index {
            return d;
        }
        let Some(text) = (self.text)() else {
            return d;
        };
        let bound: Vec<LocalId> = block[index..change].iter().flat_map(binds).collect();
        let uses = |s: &Stmt| {
            walk::stmt_exprs(s).into_iter().any(|e| {
                walk::exists(
                    e,
                    &|x| matches!(x.kind, ExprKind::Local(v) if bound.contains(&v)),
                )
            })
        };
        let binding = block[index].at;
        let what = if reaches { "access" } else { "change" };
        let mut d = d;
        if !uses(&block[change])
            && let Some(fix) = move_before(&text, binding, block[change].at, what)
        {
            d = d.with_fix(fix);
        }
        if !block[change..].iter().any(uses) {
            let edits = vec![
                Edit::insert(binding.start(), "{ "),
                Edit::insert(block[change - 1].at.end(), " }"),
            ];
            let says = format!("end the view's scope before the {what}");
            d = d.with_fix(Fix::new(says, edits));
        }
        d
    }
}

/// The variables that a statement binds.
fn binds(s: &Stmt) -> Vec<LocalId> {
    let mut vars = Vec::new();
    if let StmtKind::Let(b) | StmtKind::Var(b) = &s.kind {
        bound_by(&b.pattern, &mut vars);
    }
    vars
}

/// The fix that moves the statement at `moved`, which holds the `what`, to before the one at
/// `binding`, on a line of its own with the same indent, deleting its own line when nothing
/// else is on it.
fn move_before(text: &str, binding: TextRange, moved: TextRange, what: &str) -> Option<Fix> {
    let written = text.get(std::ops::Range::<usize>::from(moved))?;
    let blanks = indent(text, binding.start())?;
    let line = indent(text, moved.start())
        .zip(text.get(usize::from(moved.end())..))
        .filter(|(_, after)| after.starts_with('\n'))
        .map_or(moved, |(blanks, _)| {
            let start = moved.start() - TextSize::of(blanks);
            TextRange::new(start, moved.end() + TextSize::from(1))
        });
    // Inserted at the start of the binding's line, the new line is all that the fix marks.
    let start = binding.start() - TextSize::of(blanks);
    let edits = vec![
        Edit::insert(start, format!("{blanks}{written}\n")),
        Edit::delete(line),
    ];
    Some(Fix::new(format!("make the {what} before the view"), edits))
}

/// The blanks before `at` on its line, if nothing else comes before it there.
fn indent(text: &str, at: TextSize) -> Option<&str> {
    let before = text.get(..usize::from(at))?;
    let start = before.rfind('\n').map_or(0, |i| i + 1);
    let blanks = &before[start..];
    blanks
        .chars()
        .all(|c| c == ' ' || c == '\t')
        .then_some(blanks)
}

/// Whether an expression is a closure literal, which may capture views (views.fixed).
fn is_closure(e: &Expr) -> bool {
    matches!(e.kind, ExprKind::Closure(..))
}
