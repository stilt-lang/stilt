//! Yielding exactly once (projections.once-on-every-path): every path through a projection's body
//! from its start to its end or to a `return` runs one `yield`, and a path that ends by raising or
//! panicking runs at most one. The check is syntactic: it follows the counts of yields that each
//! path can have reached, 0, 1 or more, through the arms of branches, and reports E0424 at a
//! `yield` inside a loop or the operand of a `try` with arms, which could run more than once or not
//! at all, at the second `yield` of a path, and at the end of the body or the `return` that a path
//! reaches without one. Rule numbers in comments refer to the Reference's projections chapter.

use stilt_diag::{Diagnostic, codes};
use stilt_syntax::{TextRange, TextSize};

use crate::tast::walk;
use crate::tast::{Block, Expr, ExprKind, Stmt, StmtKind};
use crate::ty::Ty;

/// The counts that the paths reaching a point have: 0, 1 or 2, which stands for more.
type Counts = Vec<u8>;

fn union(a: Counts, b: &Counts) -> Counts {
    let mut all = a;
    for &c in b {
        if !all.contains(&c) {
            all.push(c);
        }
    }
    all.sort_unstable();
    all
}

fn stepped(counts: &Counts) -> Counts {
    counts.iter().map(|c| (c + 1).min(2)).collect()
}

struct Yields<'a> {
    /// The construct a `yield` here would be inside, which could run it more than once or not
    /// at all: a loop, or a `try` with arms.
    inside: Option<&'a str>,
    found: Vec<Diagnostic>,
}

/// projections.once-on-every-path: the errors of a projection's body, whose closing brace ends at
/// `end`.
pub(super) fn errors(block: &Block, end: TextSize) -> Vec<Diagnostic> {
    let mut y = Yields {
        inside: None,
        found: Vec::new(),
    };
    let counts = y.block(vec![0], block);
    if counts.contains(&0) {
        let brace = TextRange::new(end - TextSize::from(1), end);
        let message = "a path through the projection reaches its end without a `yield`: every \
                       path yields exactly once";
        y.found.push(Diagnostic::new(codes::E0424, brace, message));
    }
    y.found
}

impl Yields<'_> {
    /// The counts after an expression, which holds yields only in its blocks and arms; an
    /// expression of type `Never` and a hole end their paths.
    fn expr(&mut self, counts: Counts, e: &Expr) -> Counts {
        let after = match &e.kind {
            ExprKind::Block(b) => self.block(counts, b),
            ExprKind::If(_, b, alt) | ExprKind::IfLet(_, _, b, alt) => {
                let then = self.block(counts.clone(), b);
                let other = match alt {
                    Some(x) => self.expr(counts, x),
                    None => counts,
                };
                union(then, &other)
            }
            ExprKind::Match(_, arms) => arms.iter().fold(Vec::new(), |acc, a| {
                let after = self.expr(counts.clone(), &a.body);
                union(acc, &after)
            }),
            ExprKind::Try(x, catch) => {
                let outer = self.inside;
                if catch.is_some() {
                    self.inside = Some("a `try` with arms");
                }
                let after = self.expr(counts, x);
                self.inside = outer;
                walk::catch_arms(catch.as_ref())
                    .iter()
                    .fold(after.clone(), |acc, a| {
                        let arm = self.expr(after.clone(), &a.body);
                        union(acc, &arm)
                    })
            }
            ExprKind::Loop(b) | ExprKind::While(_, b) | ExprKind::For(_, _, b) => {
                let outer = self.inside.replace("a loop");
                let after = self.block(counts.clone(), b);
                self.inside = outer;
                // A yield in the body, reported there, counts as the one yield of the paths
                // through the loop.
                if after == counts {
                    counts
                } else {
                    stepped(&counts)
                }
            }
            ExprKind::Return(_) => {
                if counts.contains(&0) {
                    let message = "this `return` ends a path through the projection that \
                                   hasn't yielded: every path yields exactly once";
                    self.found
                        .push(Diagnostic::new(codes::E0424, e.at, message));
                }
                counts
            }
            _ => counts,
        };
        // A hole panics when reached, so its path runs at most one `yield`.
        if e.ty == Ty::never() || matches!(e.kind, ExprKind::Hole) {
            Vec::new()
        } else {
            after
        }
    }

    fn stmt(&mut self, counts: Counts, s: &Stmt) -> Counts {
        match &s.kind {
            StmtKind::Yield(_) => {
                if let Some(what) = self.inside {
                    let message = format!(
                        "this `yield` is inside {what}, so it could run more than once or not \
                         at all: a projection yields exactly once"
                    );
                    self.found
                        .push(Diagnostic::new(codes::E0424, s.at, message));
                }
                if counts.iter().any(|&c| c >= 1) {
                    let message = "this path through the projection has yielded already: a \
                                   projection yields exactly once";
                    self.found
                        .push(Diagnostic::new(codes::E0424, s.at, message));
                }
                stepped(&counts)
            }
            StmtKind::Let(b) | StmtKind::Var(b) => {
                let counts = self.expr(counts, &b.value);
                match &b.otherwise {
                    Some(o) => self.expr(counts, o),
                    None => counts,
                }
            }
            StmtKind::Assign(_, p, v) => {
                let counts = self.expr(counts, p);
                self.expr(counts, v)
            }
            StmtKind::Assert(e) | StmtKind::Expr(e) => self.expr(counts, e),
        }
    }

    fn block(&mut self, counts: Counts, b: &Block) -> Counts {
        b.iter().fold(counts, |counts, s| self.stmt(counts, s))
    }
}
