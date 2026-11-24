//! Known signs (facts.known-signs): the integer expressions known non-negative, and those known
//! positive, each in the body it is evaluated in. A binding is known non-negative by the greatest
//! fixed point: the bindings count on one another and on themselves, so `a = a + 1` keeps `a`
//! known non-negative, as `a += 1` does.

use std::collections::BTreeSet;

use stilt_hir::hir::{BinaryOp, LocalId};

use super::Context;
use super::code::Reader;
use super::walked::{Declared, Walked, WriteKind};
use crate::tast::{Callee, Expr, ExprKind};

/// The bindings known non-negative.
pub(super) struct Signs<'s, 'a> {
    walked: &'s Walked<'a>,
    reader: Reader<'s>,
    nonneg: BTreeSet<LocalId>,
}

impl<'s, 'a> Signs<'s, 'a> {
    pub(super) fn of(cx: &'s Context<'s>, walked: &'s Walked<'a>) -> Self {
        let mut signs = Signs {
            walked,
            reader: Reader {
                cx,
                whens: &walked.whens,
            },
            nonneg: walked.decls.keys().copied().collect(),
        };
        loop {
            let lost: Vec<LocalId> = (walked.decls.iter())
                .filter(|(v, _)| signs.nonneg.contains(v))
                .filter(|(v, (body, d))| !signs.binding_nonneg(**v, *body, d))
                .map(|(v, _)| *v)
                .collect();
            if lost.is_empty() {
                return signs;
            }
            for v in lost {
                signs.nonneg.remove(&v);
            }
        }
    }

    pub(super) fn reader(&self) -> &Reader<'s> {
        &self.reader
    }

    /// Whether a `let` or a `var` binding of the body `body` is known non-negative: its initial
    /// value is, and the body writes it only by `=` or `+=` of known non-negative expressions.
    fn binding_nonneg(&self, v: LocalId, body: u32, d: &Declared<'_>) -> bool {
        let init = match d {
            Declared::Let(e) | Declared::Var(e) => e,
            Declared::Range(_) => return false,
        };
        self.nonneg(init, body)
            && (self.walked.log.iter())
                .filter(|w| w.body == body && w.root == v)
                .all(|w| {
                    w.fields.is_empty()
                        && !w.indexed
                        && matches!(w.kind, WriteKind::Assign(None | Some(BinaryOp::Add)))
                        && w.value.is_some_and(|e| self.nonneg(e, body))
                })
    }

    /// Whether an expression evaluated in the body `body` is known non-negative.
    pub(super) fn nonneg(&self, e: &Expr, body: u32) -> bool {
        if let Some(n) = self.reader.number(e) {
            return n >= 0;
        }
        match &e.kind {
            ExprKind::Call(c, _, args, _) => is_len(c) && args.len() == 1,
            ExprKind::Local(v) => match self.walked.decls.get(v) {
                Some((b, Declared::Range(start))) if *b == body => self.nonneg(start, body),
                Some((b, _)) if *b == body => self.nonneg.contains(v),
                _ => false,
            },
            ExprKind::Binary(BinaryOp::Add | BinaryOp::Mul, a, b) => {
                self.nonneg(a, body) && self.nonneg(b, body)
            }
            _ => false,
        }
    }

    /// Whether an expression evaluated in the body `body` is known positive.
    pub(super) fn positive(&self, e: &Expr, body: u32) -> bool {
        if let Some(n) = self.reader.number(e) {
            return n > 0;
        }
        match &e.kind {
            ExprKind::Local(v) => matches!(
                self.walked.decls.get(v),
                Some((b, Declared::Range(start))) if *b == body && self.positive(start, body)
            ),
            _ => false,
        }
    }
}

/// Whether a callee is a method `len`.
fn is_len(c: &Callee) -> bool {
    super::code::method(c) == Some("len")
}
