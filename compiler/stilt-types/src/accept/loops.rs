//! Counting loops (facts.counting-loops): a `while` whose condition compares a counter with a bound
//! that the loop doesn't change, and whose body steps the counter toward the bound by a known
//! positive amount, once, before any `continue`.

use stilt_hir::hir::{BinaryOp, LocalId};
use stilt_syntax::{TextRange, TextSize};

use super::indexes::{Rules, first};
use super::walked::{Declared, Looped, Write};
use super::{Need, Rule, Verdict};
use crate::tast::walk::{Part, parts};
use crate::tast::{Expr, ExprKind, Stmt, StmtKind};

impl Rules<'_, '_> {
    /// The verdict of each `while` and `loop`.
    pub(super) fn loops(&self) -> Vec<(TextRange, Verdict)> {
        (self.walked.loops.iter())
            .map(|l| {
                let verdict = match self.counting(l) {
                    Ok(()) => Verdict::Proved(Rule::CountingLoop),
                    Err(need) => Verdict::Lacks(need),
                };
                (l.at, verdict)
            })
            .collect()
    }

    /// Whether the loop counts toward its bound, or what the counting loop needs.
    fn counting(&self, l: &Looped<'_>) -> Result<(), Need> {
        let mut head = l.cond.ok_or(Need::Comparison)?;
        while let ExprKind::Binary(BinaryOp::And, a, _) = &head.kind {
            head = a;
        }
        let ExprKind::Binary(op, a, b) = &head.kind else {
            return Err(Need::Comparison);
        };
        let grows = match op {
            BinaryOp::Lt | BinaryOp::Le => true,
            BinaryOp::Gt | BinaryOp::Ge => false,
            _ => return Err(Need::Comparison),
        };
        let mut best: Option<(u8, Need)> = None;
        for (v, bound, grows) in [(a, b, grows), (b, a, !grows)] {
            let Some(v) = self.counter(l, v) else {
                continue;
            };
            match self.counts(l, v, bound, grows) {
                Ok(()) => return Ok(()),
                Err((stage, need)) if best.as_ref().is_none_or(|(s, _)| stage > *s) => {
                    best = Some((stage, need));
                }
                Err(_) => {}
            }
        }
        Err(best.map_or(Need::CounterVar, |(_, need)| need))
    }

    /// The counter a side of the comparison names: a `var` of an integer type of the loop's
    /// body.
    fn counter(&self, l: &Looped<'_>, e: &Expr) -> Option<LocalId> {
        let v = self.signs.reader().name(e)?;
        match self.walked.decls.get(&v) {
            Some((body, Declared::Var(_))) if *body == l.body => Some(v),
            _ => None,
        }
    }

    /// Whether the counter `v` counts toward `bound`, or the stage of the first condition it
    /// fails, with what it needs.
    fn counts(
        &self,
        l: &Looped<'_>,
        v: LocalId,
        bound: &Expr,
        grows: bool,
    ) -> Result<(), (u8, Need)> {
        self.bound(l, bound).map_err(|at| (1, Need::Bound(at)))?;
        let Some((step, s)) = self.step(l, v, grows) else {
            return Err((2, Need::Step(v, grows)));
        };
        let before = &l.block[..step];
        if let Some(at) = continues(before) {
            return Err((3, Need::ContinueBefore(v, grows, s.at, at)));
        }
        let step_at = l.block[step].at;
        let elsewhere = first(self.walked.in_span(l.body, l.span), &|w| {
            w.root == v && !step_at.contains(w.at)
        });
        match elsewhere {
            Some(at) => Err((4, Need::CounterWrites(v, at))),
            None => Ok(()),
        }
    }

    /// Whether the bound is made of literals, constants, names of bindings that the loop
    /// doesn't write, and lengths of places whose length it doesn't change, by `+`, `-` and
    /// `*`; or where the loop changes it, if it does.
    fn bound(&self, looped: &Looped<'_>, e: &Expr) -> Result<(), Option<TextSize>> {
        let reader = self.signs.reader();
        let writes = |holds: &dyn Fn(&Write<'_>) -> bool| {
            first(self.walked.in_span(looped.body, looped.span), holds)
                .map_or(Ok(()), |at| Err(Some(at)))
        };
        if let Some(binding) = reader.binding(e) {
            return writes(&|w| w.root == binding);
        }
        if let Some(place) = reader.len_of(e) {
            return writes(&|w| w.changes(&place));
        }
        match &e.kind {
            ExprKind::Int(_) | ExprKind::Constant(_) | ExprKind::MemberConstant(..) => Ok(()),
            ExprKind::Unary(stilt_hir::hir::UnaryOp::Neg, operand)
                if matches!(operand.kind, ExprKind::Int(_)) =>
            {
                Ok(())
            }
            ExprKind::Binary(BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul, left, right) => {
                match (self.bound(looped, left), self.bound(looped, right)) {
                    (Err(Some(one)), Err(Some(other))) => Err(Some(one.min(other))),
                    (Err(None), _) | (_, Err(None)) => Err(None),
                    (Err(at), Ok(())) | (Ok(()), Err(at)) => Err(at),
                    (Ok(()), Ok(())) => Ok(()),
                }
            }
            _ => Err(None),
        }
    }

    /// The first statement of the loop's own block that steps the counter: `v += s` where it
    /// grows and `v -= s` where it falls, with `s` known positive; with `s`.
    fn step<'b>(&self, l: &Looped<'b>, v: LocalId, grows: bool) -> Option<(usize, &'b Expr)> {
        let op = if grows { BinaryOp::Add } else { BinaryOp::Sub };
        l.block.iter().enumerate().find_map(|(i, s)| match &s.kind {
            StmtKind::Assign(Some(o), place, s)
                if *o == op
                    && matches!(place.kind, ExprKind::Local(x) if x == v)
                    && self.signs.positive(s, l.body) =>
            {
                Some((i, s))
            }
            _ => None,
        })
    }
}

/// Where the first `continue` of a loop is among `stmts`, outside the loops and closure
/// literals inside them.
fn continues(stmts: &[Stmt]) -> Option<TextSize> {
    let mut found = None;
    for s in stmts {
        for e in crate::tast::walk::stmt_exprs(s) {
            continue_in(e, &mut found);
        }
    }
    found
}

fn continue_in(e: &Expr, found: &mut Option<TextSize>) {
    match &e.kind {
        ExprKind::Continue => {
            let at = e.at.start();
            *found = Some(found.map_or(at, |f: TextSize| f.min(at)));
        }
        ExprKind::While(..) | ExprKind::Loop(_) | ExprKind::For(..) | ExprKind::Closure(..) => {}
        _ => {
            for part in parts(e) {
                match part {
                    Part::Expr(x) => continue_in(x, found),
                    Part::Block(b) => {
                        if let Some(at) = continues(b) {
                            *found = Some(found.map_or(at, |f| f.min(at)));
                        }
                    }
                }
            }
        }
    }
}
