//! Branches and loops in the walk. Rule numbers in comments refer to the Reference's chapter on
//! modes, unless they name another record.

use stilt_hir::hir::{BinaryOp, LocalId};
use stilt_syntax::{TextRange, TextSize};
use stilt_types::tast::walk::catch_arms;
use stilt_types::tast::{Arm, Block, Expr, ExprKind, Iterable, Pat};

use super::super::places::{self, Step, binders, pattern_parts};
use super::super::{END, Holder, How, Into, Kind, Modification, Tick, Write};
use super::{Target, Walk, scope};

impl Walk<'_> {
    /// The expressions that decide what runs next: jumps, branches and loops, and the blocks of
    /// a `with` and a `when`.
    pub(super) fn control(&mut self, e: &Expr, into: &Into<'_>) {
        let read = Into::read(e.at.end());
        match &e.kind {
            ExprKind::Return(v) => {
                if let Some(v) = v {
                    self.expr(v, &Into::leaving(How::Returned));
                }
                self.jump(e.at.end());
            }
            ExprKind::Raise(v) => {
                self.expr(v, &Into::leaving(How::Raised));
                self.jump(e.at.end());
            }
            ExprKind::Break | ExprKind::Continue => self.leave(e),
            ExprKind::Block(b) => self.block(b, into),
            ExprKind::If(c, b, alt) => {
                self.expr(c, &read);
                let other = alt.as_ref().map_or(e.at.end(), |x| x.at.start());
                let at = [scope(b, e.at.start()).start(), other, e.at.end()];
                self.either(
                    at,
                    |w| w.block(b, into),
                    |w| alt.iter().for_each(|x| w.expr(x, into)),
                );
            }
            ExprKind::Else(a, b) => {
                self.expr(a, into);
                let at = [b.at.start(), e.at.end(), e.at.end()];
                self.either(at, |w| w.expr(b, into), |_| {});
            }
            ExprKind::Binary(BinaryOp::And | BinaryOp::Or, a, b) => {
                self.expr(a, &read);
                let at = [b.at.start(), e.at.end(), e.at.end()];
                self.either(at, |w| w.expr(b, &read), |_| {});
            }
            ExprKind::With(..) => self.handled(e.at, |w| w.parts(e, &read)),
            ExprKind::When(held, b) => self.held(e, held, b, into),
            ExprKind::IfLet(..) | ExprKind::Match(..) | ExprKind::Try(..) => {
                self.branches(e, into);
            }
            ExprKind::Loop(_) | ExprKind::While(..) | ExprKind::For(..) => self.looping(e),
            _ => self.parts(e, &read),
        }
    }

    /// A `when`'s names stand for the places of the shared values, which its block may modify
    /// as a `var` (shared.when): each is bound where the block starts. Its value goes back to the
    /// handle when the block ends, where later `when`s may write it, so what it holds lasts on,
    /// and the end of the block modifies each name (modes.handles). The block's value is the
    /// `when`'s, held by what holds it, so that a copy of a name the block gives lasts there.
    fn held(&mut self, e: &Expr, held: &[(Expr, LocalId)], b: &Block, into: &Into<'_>) {
        let read = Into::read(e.at.end());
        for (x, _) in held {
            self.expr(x, &read);
        }
        let bound: Vec<LocalId> = held.iter().map(|(_, v)| *v).collect();
        for (i, (x, v)) in held.iter().enumerate() {
            let same = held[i + 1..].iter().filter(|(y, _)| y.ty == x.ty);
            self.flow.joined.extend(same.map(|(_, w)| (*v, *w)));
        }
        let at = scope(b, into.lasts);
        self.bind_at(&bound, at.start());
        for &v in &bound {
            self.declare(v, Kind::Var, TextRange::new(at.start(), END));
        }
        let given = Into {
            held: Some(into.keeper()),
            leaves: into.leaves.clone(),
            result: into.result.clone(),
            pattern: into.pattern,
            lasts: into.lasts,
            at: into.at.clone(),
        };
        self.block(b, &given);
        let keyword = TextRange::at(e.at.start(), TextSize::of("when"));
        let tick = self.tick(e.at.end());
        for v in bound {
            self.flow.writes.push(Write {
                binding: v,
                path: Vec::new(),
                at: keyword,
                tick,
                replaces: false,
                how: Modification::WhenEnd,
            });
        }
    }

    /// `if let`, `match` and `try`, whose branches' values go where the whole's goes. A raise, or
    /// a call that may raise, anywhere in a `try`'s operand goes to its arms (modes.shared-writes).
    fn branches(&mut self, e: &Expr, into: &Into<'_>) {
        let read = Into::read(e.at.end());
        match &e.kind {
            ExprKind::IfLet(p, scrutinee, b, alt) => {
                let bound = scope(b, e.at.end());
                self.matched(scrutinee, &[(p, bound)]);
                let other = alt.as_ref().map_or(e.at.end(), |x| x.at.start());
                let at = [bound.start(), other, e.at.end()];
                self.either(
                    at,
                    |w| w.block(b, into),
                    |w| alt.iter().for_each(|x| w.expr(x, into)),
                );
            }
            ExprKind::Match(scrutinee, arms) => {
                let bound: Vec<(&Pat, TextRange)> =
                    arms.iter().map(|a| (&a.pattern, a.body.at)).collect();
                self.matched(scrutinee, &bound);
                let choice = self.here();
                let arms: Vec<&Arm> = arms.iter().collect();
                self.arms(&[choice], &arms, |_, _| {}, vec![], into, e.at.end());
            }
            ExprKind::Try(operand, catch) => {
                let first = self.here();
                self.expr(operand, into);
                let last = self.here();
                let arms: Vec<&Arm> = catch_arms(catch.as_ref()).iter().collect();
                let enter = |w: &mut Self, (entry, a): (Tick, &Arm)| {
                    w.flow.paths.ranges.push((first, last, entry));
                    let bound = binders(&a.pattern);
                    w.bind_at(&bound, a.body.at.start());
                    for v in bound {
                        w.declare(v, Kind::Pattern, a.body.at);
                    }
                };
                self.arms(&[], &arms, enter, vec![last], into, e.at.end());
            }
            _ => self.parts(e, &read),
        }
    }

    /// Arms, each entered from `entries` and from the guards of the arms before it, after which
    /// control meets `ends`, at `end`. `enter` walks what each arm binds before it.
    fn arms(
        &mut self,
        entries: &[Tick],
        arms: &[&Arm],
        mut enter: impl FnMut(&mut Self, (Tick, &Arm)),
        mut ends: Vec<Tick>,
        into: &Into<'_>,
        end: TextSize,
    ) {
        let mut froms = entries.to_vec();
        for a in arms {
            let entry = self.meet(a.body.at.start(), &froms, &[]);
            enter(self, (entry, a));
            if let Some(guard) = &a.guard {
                self.expr(guard, &Into::read(guard.at.end()));
                froms.push(self.here());
            }
            self.expr(&a.body, into);
            ends.push(self.here());
        }
        self.meet(end, &ends, &[]);
    }

    /// A value that patterns match, each binding for its scope.
    fn matched(&mut self, scrutinee: &Expr, patterns: &[(&Pat, TextRange)]) {
        self.expr(scrutinee, &Into::read(scrutinee.at.end()));
        self.bind_parts(scrutinee, patterns, false);
    }

    /// The parts of a value that patterns bind, each binding for its scope, bound anew where
    /// they are bound. When the value is a place of a binding, each part a pattern binds is a
    /// copy, held by the variable that binds it (modes.copies); with `element`, the patterns bind
    /// its elements.
    fn bind_parts(&mut self, scrutinee: &Expr, patterns: &[(&Pat, TextRange)], element: bool) {
        let bound: Vec<_> = patterns.iter().flat_map(|(p, _)| binders(p)).collect();
        self.bind_at(&bound, scrutinee.at.end());
        for (p, scope) in patterns {
            for v in binders(p) {
                self.declare(v, Kind::Pattern, *scope);
            }
        }
        let Some((root, mut path)) = places::place(scrutinee) else {
            return;
        };
        if self.own(root).is_none() || !self.calls.cow(&scrutinee.ty) {
            return;
        }
        if element {
            path.push(Step::Index);
        }
        let at = scrutinee.at.start();
        let made = (at, self.tick(at));
        for (p, scope) in patterns {
            let mut parts = Vec::new();
            pattern_parts(p, &path, &mut parts);
            for (part, v, ty) in parts {
                if self.calls.cow(&ty) {
                    let holder = Holder::Bound(vec![v], *scope);
                    self.copy(root, part, made, holder, false, Some(Vec::new()));
                }
            }
        }
    }

    /// A loop, whose body runs again after any code of it. A `while`'s condition runs at its
    /// head, where the loop may end. A `for` loop's iterable is evaluated once, before; a place it
    /// is is read for the whole body (modes.durations), and its pattern binds each element anew at
    /// the head, where the loop may end.
    fn looping(&mut self, e: &Expr) {
        let read = Into::read(e.at.end());
        match &e.kind {
            ExprKind::Loop(b) => self.turns(e, |_, _| vec![], |w| w.block(b, &read)),
            ExprKind::While(c, b) => {
                let start = |w: &mut Self, _| {
                    w.expr(c, &read);
                    let tested = w.here();
                    w.meet(c.at.end(), &[tested], &[]);
                    vec![tested]
                };
                self.turns(e, start, |w| w.block(b, &read));
            }
            ExprKind::For(p, iterable, b) => match &**iterable {
                Iterable::Iter(source) => {
                    self.expr(source, &Into::read(source.at.end()));
                    let bound = TextRange::new(source.at.end(), e.at.end());
                    let start = |w: &mut Self, head| {
                        if let Some((root, _)) = places::place(source) {
                            let at = w.tick(source.at.start());
                            w.flow.reads.push((root, at));
                        }
                        w.bind_parts(source, &[(p, bound)], true);
                        vec![head]
                    };
                    self.turns(e, start, |w| w.block(b, &read));
                }
                Iterable::Range(from, to, _) => {
                    self.expr(from, &read);
                    self.expr(to, &read);
                    let bound = TextRange::new(to.at.end(), e.at.end());
                    for v in binders(p) {
                        self.declare(v, Kind::Pattern, bound);
                    }
                    let start = |w: &mut Self, head| {
                        w.bind_at(&binders(p), to.at.end());
                        vec![head]
                    };
                    self.turns(e, start, |w| w.block(b, &read));
                }
            },
            _ => self.parts(e, &read),
        }
    }

    /// A loop's turns (modes.shared-writes): its head is reached from before the loop, from the
    /// end of each turn and from each `continue`, and what follows the loop from where `start`,
    /// which walks what runs at the head, says, and from each `break`.
    fn turns(
        &mut self,
        e: &Expr,
        start: impl FnOnce(&mut Self, Tick) -> Vec<Tick>,
        body: impl FnOnce(&mut Self),
    ) {
        let before = self.here();
        let head = self.meet(e.at.start(), &[before], &[]);
        self.targets.push(Target {
            head,
            breaks: Vec::new(),
            continues: Vec::new(),
        });
        let exits = start(self, head);
        body(self);
        let end = self.here();
        self.step(end, head);
        let target = self.targets.pop().expect("the loop's target was pushed");
        let back = target.continues.iter().map(|&c| (c, target.head));
        self.flow.paths.links.extend(back);
        self.meet(e.at.end(), &exits, &target.breaks);
    }
}
