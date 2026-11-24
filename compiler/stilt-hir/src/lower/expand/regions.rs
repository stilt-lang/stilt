//! The texts of expansions being resolved, each placed past the end of every file, and how a
//! position in one is reported and what its names mean (macros.hygiene and
//! macros.errors-in-expansions).
//!
//! An expansion's tree is resolved as code is, its positions offset into a region of its own,
//! so that each name in it can be told by its position: one the user wrote, in a fragment, or
//! one the template wrote. When the expansion is resolved, every position in its region is
//! moved to the tokens the user wrote: a span inside a fragment's tokens to them, and any other
//! to the use.

use rustc_hash::FxHashSet;
use stilt_syntax::{TextRange, TextSize};

use super::super::Resolver;
use crate::hir::{Ident, Name};
use crate::macros::substitute::Tok;
use crate::scope::Scope;

/// Where expansions' regions start: past the end of every file.
pub(super) const VIRTUAL: u32 = 1 << 31;

/// An expansion being resolved.
pub(crate) struct Region {
    /// Where its text starts.
    pub(super) base: TextSize,
    /// Where each of its tokens starts and ends in its text.
    pub(super) spans: Vec<TextRange>,
    pub(super) tokens: Vec<Tok>,
    /// The marks of the names its own tokens write, each with the module where they resolve:
    /// the macro's for a template's, and the module of the quote that wrote them for a
    /// procedural macro's (macros.quote-hygiene).
    pub(super) marks: Vec<(u32, Name)>,
    /// The macro, as its use names it.
    pub(super) name: Name,
    /// The index of the expansion among the body's.
    pub(super) index: usize,
    /// The names its own tokens bind, each with its mark, which are fresh.
    pub(super) fresh: FxHashSet<(u32, Name)>,
    /// Whether a procedural macro made it, whose fresh names are numbered in the order their
    /// bindings appear in it, and not by its mark (macros.showing).
    pub(super) procedural: bool,
}

impl Region {
    fn len(&self) -> TextSize {
        self.spans.last().map_or(TextSize::default(), |s| s.end())
    }

    /// The mark `mark` of its own tokens, with the module where its names resolve. Its marks
    /// are made in increasing order.
    fn mark(&self, mark: u32) -> Option<&(u32, Name)> {
        let i = self.marks.binary_search_by_key(&mark, |(m, _)| *m).ok()?;
        self.marks.get(i)
    }

    /// Whether a position is in the region's text.
    pub(super) fn holds_at(&self, at: TextSize) -> bool {
        at >= self.base && at <= self.base + self.len()
    }

    /// The tokens a span of the region covers, from the first to just past the last.
    pub(super) fn place_tokens(&self, range: TextRange) -> (u32, u32) {
        let covered = self.covered(range);
        let index = |i: usize| u32::try_from(i).unwrap_or(u32::MAX);
        (index(covered.start), index(covered.end))
    }

    /// The tokens a span of the region covers, by index: those it overlaps, or for an empty
    /// span, the one it touches.
    fn covered(&self, range: TextRange) -> std::ops::Range<usize> {
        let start = range.start() - self.base;
        let end = range.end() - self.base;
        let first = self.spans.partition_point(|s| s.end() <= start);
        let last = if end > start {
            self.spans.partition_point(|s| s.start() < end)
        } else {
            first + 1
        };
        first.min(self.spans.len().saturating_sub(1))..last.max(first + 1).min(self.spans.len())
    }

    /// Where a span of the region is reported, and whether the user wrote all of it: a span of
    /// a fragment's tokens at them, and any other where the first token the template wrote is.
    pub(super) fn place(&self, range: TextRange) -> (TextRange, bool) {
        let covered = &self.tokens[self.covered(range)];
        match covered.iter().find(|t| !t.user) {
            Some(own) => (own.at, false),
            None => match (covered.first(), covered.last()) {
                (Some(first), Some(last)) if first.at.start() <= last.at.end() => {
                    (TextRange::new(first.at.start(), last.at.end()), true)
                }
                (Some(first), _) => (first.at, true),
                _ => (TextRange::default(), true),
            },
        }
    }
}

impl<'a> Resolver<'a> {
    /// The expansion being resolved whose region holds a position.
    pub(super) fn region_at(&self, at: TextSize) -> Option<&Region> {
        if u32::from(at) < VIRTUAL {
            return None;
        }
        self.regions.iter().rev().find(|r| r.holds_at(at))
    }

    /// The mark of the name written at `at`: 0 for the user's, and its expansion's for one a
    /// template wrote (macros.hygiene).
    pub(in crate::lower) fn mark_of(&self, at: TextRange) -> u32 {
        self.region_at(at.start()).map_or(0, |r| {
            let i = r.covered(at).start;
            r.tokens.get(i).map_or(0, |t| t.mark)
        })
    }

    /// The name a variable is bound under in scope: its own for the user's, and with its mark
    /// for a template's, so that neither finds the other's (macros.hygiene). Each is made once.
    pub(in crate::lower) fn key(&self, n: &Ident) -> Name {
        match self.mark_of(n.at) {
            0 => n.name,
            mark => *self
                .keys
                .borrow_mut()
                .entry((n.name, mark))
                .or_insert_with(|| Name::from(format!("{}#{mark}", n.name))),
        }
    }

    /// The module where the items that a name written at `at` names are found, and its scope:
    /// the module's own for the user's names, and the macro's module for a template's.
    pub(in crate::lower) fn home(&self, at: TextRange) -> (Name, &'a Scope) {
        let mark = self.mark_of(at);
        let own = (self.module.name, self.own);
        if mark == 0 {
            return own;
        }
        let found = self.regions.iter().find_map(|r| r.mark(mark));
        match found {
            Some((_, home)) if *home == self.module.name => own,
            Some((_, home)) => self.scope_of(home).map_or(own, |scope| (*home, scope)),
            None => own,
        }
    }

    /// Records that a template binds `name` in the expansion of `mark`, a fresh name.
    pub(in crate::lower) fn bound_fresh(&mut self, at: TextRange, name: Name) {
        let mark = self.mark_of(at);
        let holds = |r: &&mut Region| r.mark(mark).is_some();
        if let Some(r) = self.regions.iter_mut().find(holds).filter(|_| mark > 0) {
            r.fresh.insert((mark, name));
        }
    }

    /// Where a position of the code being resolved is reported, and whether the user wrote
    /// all of it.
    pub(super) fn placed(&self, at: TextRange) -> (TextRange, bool) {
        match self.region_at(at.start()) {
            Some(r) => r.place(at),
            None => (at, true),
        }
    }
}
