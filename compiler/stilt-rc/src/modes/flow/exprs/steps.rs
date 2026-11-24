//! The steps of the paths that execution may take, which the walk adds as it meets jumps,
//! branches and loops (modes.shared-writes). Rule numbers in comments refer to the Reference's
//! chapter on modes, unless they name another record.

use stilt_hir::hir::LocalId;
use stilt_syntax::{TextRange, TextSize};
use stilt_types::tast::{Expr, ExprKind};

use super::super::Tick;
use super::Walk;

impl Walk<'_> {
    /// A new tick, at `at` in the source.
    pub(super) fn tick(&mut self, at: TextSize) -> Tick {
        self.flow.paths.at.push(at);
        self.here()
    }

    /// The last tick so far.
    pub(super) fn here(&self) -> Tick {
        Tick::try_from(self.flow.paths.at.len() - 1).unwrap_or(Tick::MAX)
    }

    /// A step from the tick `a` to `b`, unless `a` is a jump (modes.shared-writes).
    pub(super) fn step(&mut self, a: Tick, b: Tick) {
        if !self.flow.paths.jumps.contains(&a) {
            self.flow.paths.links.push((a, b));
        }
    }

    /// A new tick, at `at`, that control reaches only from the ticks `froms`, the ends of the
    /// paths that meet there, unless one is a jump, and from the jumps `jumps`.
    pub(super) fn meet(&mut self, at: TextSize, froms: &[Tick], jumps: &[Tick]) -> Tick {
        let t = self.tick(at);
        self.flow.paths.cut.insert(t - 1);
        for &a in froms {
            self.step(a, t);
        }
        self.flow.paths.links.extend(jumps.iter().map(|&j| (j, t)));
        t
    }

    /// A new tick, at `at`, that goes on to nothing that follows it in the source.
    pub(super) fn jump(&mut self, at: TextSize) -> Tick {
        let t = self.tick(at);
        self.flow.paths.cut.insert(t);
        self.flow.paths.jumps.insert(t);
        t
    }

    /// Where bindings are bound, at `at`, which starts them anew.
    pub(super) fn bind_at(&mut self, vars: &[LocalId], at: TextSize) {
        let t = self.tick(at);
        self.flow.bound.extend(vars.iter().map(|&v| (v, t)));
    }

    /// A `break` goes to what follows its loop, and a `continue` to its loop's head
    /// (modes.shared-writes).
    pub(super) fn leave(&mut self, e: &Expr) {
        let j = self.jump(e.at.start());
        if let Some(t) = self.targets.last_mut() {
            match e.kind {
                ExprKind::Break => t.breaks.push(j),
                _ => t.continues.push(j),
            }
        }
    }

    /// Two alternatives after the tick where control chooses, at `at`: each path goes through
    /// one of them, and they meet after.
    pub(super) fn either(
        &mut self,
        at: [TextSize; 3],
        first: impl FnOnce(&mut Self),
        second: impl FnOnce(&mut Self),
    ) {
        let choice = self.here();
        self.meet(at[0], &[choice], &[]);
        first(self);
        let ended = self.here();
        self.meet(at[1], &[choice], &[]);
        second(self);
        let other = self.here();
        self.meet(at[2], &[ended, other], &[]);
    }

    /// Code that may run any number of times, none among them, at `at`.
    pub(super) fn again(&mut self, at: TextRange, f: impl FnOnce(&mut Self)) {
        let before = self.here();
        let head = self.meet(at.start(), &[before], &[]);
        f(self);
        let end = self.here();
        self.step(end, head);
        self.meet(at.end(), &[head], &[]);
    }

    /// Code, at `at`, from any point of which control may go on to what follows it, as a
    /// performance in a `with`'s block that the handler doesn't resume does.
    pub(super) fn handled(&mut self, at: TextRange, f: impl FnOnce(&mut Self)) {
        let first = self.here();
        f(self);
        let last = self.here();
        let out = self.meet(at.end(), &[last], &[]);
        self.flow.paths.ranges.push((first, last, out));
    }
}
