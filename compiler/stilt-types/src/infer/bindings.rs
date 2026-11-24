//! The bindings of the expected type that a mismatch lists as its admissible alternatives (goal
//! admissible-alternatives): once the body is checked, those in scope where the mismatch is whose
//! type is the type the code expected there.

use stilt_diag::{Alternative, AlternativeKind};
use stilt_hir::hir::walk::{Visitor, walk_expr};
use stilt_hir::hir::{
    self, Block, BodyValue, ExprKind, Iterable, ListRest, LocalId, PatKind, StmtKind,
};
use stilt_syntax::TextRange;

use super::State;
use crate::ty::Ty;

impl State<'_> {
    /// Adds to each mismatch the bindings in scope at it whose type is the one it expected,
    /// if that type is known: of two of one name, the later, which hides the other.
    pub(super) fn offer_bindings(&mut self, body: &hir::Body) {
        let mismatches = std::mem::take(&mut self.mismatches);
        for (index, expected) in mismatches {
            let expected = self.table.freeze(&expected);
            if unknown(&expected) {
                continue;
            }
            let at = self.errors[index].range;
            let scope = visible(body, at);
            let found: Vec<Alternative> = scope
                .iter()
                .enumerate()
                .filter(|&(i, v)| {
                    let name = &self.local_names[v.0 as usize];
                    !scope[i + 1..]
                        .iter()
                        .any(|w| self.local_names[w.0 as usize] == *name)
                })
                .filter_map(|(_, v)| {
                    let ty = self.table.freeze(self.locals.get(v)?);
                    (ty == expected).then(|| {
                        let name = &self.local_names[v.0 as usize];
                        Alternative::new(AlternativeKind::Binding, &**name).of_type(self.show(&ty))
                    })
                })
                .collect();
            let d = self.errors[index].clone();
            self.errors[index] = d.with_alternatives(found);
        }
    }
}

/// Whether a type holds a variable that checking didn't solve.
fn unknown(t: &Ty) -> bool {
    match t {
        Ty::Var(_) | Ty::Error => true,
        Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().any(unknown),
        Ty::Fn(f) => unknown(&f.ret) || f.params.iter().any(|(_, t)| unknown(t)),
        Ty::Spread(s) => unknown(&s.pack) || unknown(&s.elem),
        Ty::Param(_) | Ty::Handler(_) | Ty::SelfTy | Ty::App(..) | Ty::Value(_) => false,
    }
}

/// The locals in scope at `at` in `body`, in the order they are bound: the parameters, then
/// the bindings of the patterns whose scope holds the innermost expression around `at`.
fn visible(body: &hir::Body, at: TextRange) -> Vec<LocalId> {
    let mut walker = Scopes {
        at,
        scope: body.params.clone(),
        found: body.params.clone(),
    };
    match &body.value {
        BodyValue::Block(b) => walker.block(b),
        BodyValue::Expr(e) | BodyValue::Property(e, _) => walker.expr(e),
    }
    walker.found
}

/// A walk that keeps the locals in scope, and the scope at the last expression around `at`
/// that it reached, which is the innermost.
struct Scopes {
    at: TextRange,
    scope: Vec<LocalId>,
    found: Vec<LocalId>,
}

impl Scopes {
    fn scoped(&mut self, inside: impl FnOnce(&mut Self)) {
        let mark = self.scope.len();
        inside(self);
        self.scope.truncate(mark);
    }

    fn block(&mut self, b: &Block) {
        self.scoped(|w| {
            for stmt in b {
                match &stmt.kind {
                    StmtKind::Let(binding) | StmtKind::Var(binding) => {
                        w.expr(&binding.value);
                        w.bind(&binding.pattern);
                    }
                    StmtKind::Assign(_, place, value) => {
                        w.expr(place);
                        w.expr(value);
                    }
                    StmtKind::Assert(e) | StmtKind::Yield(e) | StmtKind::Expr(e) => w.expr(e),
                }
            }
        });
    }

    fn arm(&mut self, arm: &hir::Arm) {
        self.scoped(|w| {
            w.bind(&arm.pattern);
            if let Some(guard) = &arm.guard {
                w.expr(guard);
            }
            w.expr(&arm.body);
        });
    }

    /// Adds the locals that `p` binds. Each alternative of an or-pattern binds the same names
    /// (patterns.or-patterns), so the first one's stand for all.
    fn bind(&mut self, p: &hir::Pat) {
        match &p.kind {
            PatKind::Bind(v) => self.scope.push(*v),
            PatKind::Tuple(ps) | PatKind::Variant(_, ps) | PatKind::Bare(_, ps, _) => {
                for q in ps {
                    self.bind(q);
                }
            }
            PatKind::Record(_, fields, _) | PatKind::AnonRecord(fields, _) => {
                for f in fields {
                    self.bind(&f.pattern);
                }
            }
            PatKind::List(ps, rest) => {
                for q in ps {
                    self.bind(q);
                }
                if let ListRest::Bind(v) = rest {
                    self.scope.push(*v);
                }
            }
            PatKind::Or(alternatives) => {
                if let Some(first) = alternatives.first() {
                    self.bind(first);
                }
            }
            PatKind::Wild
            | PatKind::Int(_)
            | PatKind::Str(_)
            | PatKind::Bool(_)
            | PatKind::Const(_)
            | PatKind::AssocConst(..)
            | PatKind::Error => {}
        }
    }
}

impl Visitor for Scopes {
    fn expr(&mut self, e: &hir::Expr) {
        if e.at.contains_range(self.at) {
            self.found.clone_from(&self.scope);
        }
        match &e.kind {
            ExprKind::Block(b) | ExprKind::Loop(b) => self.block(b),
            ExprKind::If(cond, body, alt) => {
                self.expr(cond);
                self.block(body);
                if let Some(alt) = alt {
                    self.expr(alt);
                }
            }
            ExprKind::IfLet(pattern, scrutinee, body, alt) => {
                self.expr(scrutinee);
                self.scoped(|w| {
                    w.bind(pattern);
                    w.block(body);
                });
                if let Some(alt) = alt {
                    self.expr(alt);
                }
            }
            ExprKind::While(cond, body) => {
                self.expr(cond);
                self.block(body);
            }
            ExprKind::For(pattern, iterable, body) => {
                match &**iterable {
                    Iterable::Iter(xs) => self.expr(xs),
                    Iterable::Range(from, to, _) => {
                        self.expr(from);
                        self.expr(to);
                    }
                }
                self.scoped(|w| {
                    w.bind(pattern);
                    w.block(body);
                });
            }
            ExprKind::Match(scrutinee, arms) => {
                self.expr(scrutinee);
                for a in arms {
                    self.arm(a);
                }
            }
            ExprKind::Try(operand, arms) => {
                self.expr(operand);
                arms.iter().flatten().for_each(|a| self.arm(a));
            }
            ExprKind::Closure(params, body) => self.scoped(|w| {
                for p in params {
                    w.bind(&p.pattern);
                }
                w.expr(body);
            }),
            _ => walk_expr(self, e),
        }
    }

    fn pat(&mut self, _: &hir::Pat) {}
}
