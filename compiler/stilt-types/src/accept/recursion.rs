//! Shrinking recursion (facts.shrinking-recursion): a function whose every self-call passes `p - s`
//! at one `let` parameter `p` under a test that bounds `p` from below, or `p + s` under one that
//! bounds it from above, with `s` known positive.

use stilt_hir::hir::{BinaryOp, LocalId, Mode};
use stilt_syntax::TextSize;

use super::code::{Cmp, Term};
use super::indexes::Rules;
use super::walked::{Op, Pending};
use super::{Need, Rule, Verdict};
use crate::tast::{Arg, ExprKind, TypedBody};

impl Rules<'_, '_> {
    /// Whether the function's self-calls shrink, when it has one.
    pub(super) fn recursion(&self, body: &TypedBody) -> Option<Verdict> {
        let calls: Vec<(&Pending<'_>, &[Arg])> = (self.walked.pending.iter())
            .filter_map(|p| match p.op {
                Op::SelfCall(args) => Some((p, args)),
                _ => None,
            })
            .collect();
        if calls.is_empty() {
            return None;
        }
        let params: Vec<(usize, LocalId)> = (0..)
            .zip(&body.params)
            .zip(&self.cx.params)
            .filter(|((_, (mode, _)), ty)| *mode == Mode::Let && ty.integer_name().is_some())
            .map(|((i, (_, v)), _)| (i, *v))
            .collect();
        let candidates: Vec<(usize, LocalId, bool)> = (params.iter())
            .filter_map(|&(i, p)| Some((i, p, self.moves(&calls, i, p)?)))
            .collect();
        let Some(&(_, p, falls)) = candidates.first() else {
            return Some(Verdict::Lacks(Need::ShrinkForm));
        };
        let unbounded = |&(_, p, falls): &(usize, LocalId, bool)| {
            (calls.iter())
                .filter(|(c, _)| !self.bounded(c, p, falls, &calls, &params))
                .map(|(c, _)| c.at.start())
                .min()
        };
        if candidates.iter().any(|c| unbounded(c).is_none()) {
            return Some(Verdict::Proved(Rule::ShrinkingRecursion));
        }
        let at: TextSize = unbounded(&candidates[0]).unwrap_or_default();
        Some(Verdict::Lacks(Need::ShrinkTest(p, falls, at)))
    }

    /// Whether every self-call passes `p - s` at `p`'s place, or every one `p + s`, with `s`
    /// known positive: whether `p` falls.
    fn moves(&self, calls: &[(&Pending<'_>, &[Arg])], at: usize, p: LocalId) -> Option<bool> {
        let mut falls = None;
        for (call, args) in calls {
            let ExprKind::Binary(op @ (BinaryOp::Add | BinaryOp::Sub), operand, step) =
                &args.get(at)?.value.kind
            else {
                return None;
            };
            let is_p = matches!(operand.kind, ExprKind::Local(v) if v == p);
            if !is_p || !self.signs.positive(step, call.body) {
                return None;
            }
            let this = *op == BinaryOp::Sub;
            if *falls.get_or_insert(this) != this {
                return None;
            }
        }
        falls
    }

    /// Whether a test that guards the call gives `p > b` or `p >= b` where `p` falls, and
    /// `p < b` or `p <= b` where it grows, for `b` a literal, a constant of facts.terms or another
    /// `let` parameter that every self-call passes unchanged.
    fn bounded(
        &self,
        call: &Pending<'_>,
        p: LocalId,
        falls: bool,
        calls: &[(&Pending<'_>, &[Arg])],
        params: &[(usize, LocalId)],
    ) -> bool {
        let ops = if falls {
            [Cmp::Gt, Cmp::Ge]
        } else {
            [Cmp::Lt, Cmp::Le]
        };
        let unchanged = |q: LocalId| {
            q != p
                && params.iter().any(|&(j, x)| {
                    x == q
                        && calls.iter().all(|(_, args)| {
                            args.get(j).is_some_and(
                                |a| matches!(a.value.kind, ExprKind::Local(y) if y == q),
                            )
                        })
                })
        };
        let valid = |b: &Term| match b {
            Term::Num(_) => true,
            Term::Name(q) => unchanged(*q),
            _ => false,
        };
        call.frames.iter().any(|&f| {
            self.walked.frames[f].atoms.iter().any(|a| match a {
                super::code::Atom::Cmp(x, op, y) => {
                    let (p, ps) = (Term::Name(p), ops.contains(op));
                    (*x == p && ps && valid(y))
                        || (*y == p && ops.contains(&op.mirrored()) && valid(x))
                }
                _ => false,
            })
        })
    }
}
