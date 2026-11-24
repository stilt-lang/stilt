//! Staging annotations (meta.static-expressions): the iterable of a `comptime for`, the conditions
//! and the scrutinees of a `comptime if`'s chain, and the scrutinee and guards of a `comptime
//! match` are static expressions, or E0349 at the first part of each that isn't one, in evaluation
//! order.
//!
//! The body is read in order, so that a `let` of a static value makes its variables static from
//! there on, and the variables that the patterns of an annotated form bind are static inside it.

use std::collections::HashSet;

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_hir::hir::LocalId;
use stilt_syntax::TextRange;

use super::views::sources::bound_by;
use crate::tast::walk::{Part, parts, stmt_exprs};
use crate::tast::{Arm, Block, Callee, Expr, ExprKind, Iterable, Segment, StmtKind, TypedBody};

/// The errors of the staging annotations of a body without errors of phase 1.
pub(crate) fn errors(body: &TypedBody, block: &Block) -> Vec<Diagnostic> {
    if body.staged.is_empty() {
        return Vec::new();
    }
    let mut walk = Walk {
        body,
        statics: HashSet::new(),
        vars: HashSet::new(),
        errors: Vec::new(),
    };
    walk.block(block);
    walk.errors
}

/// Why an expression isn't static, as E0349 says it.
enum Reason {
    Param(String),
    Var(String),
    Bound(String),
    Performs,
    Runs(&'static str),
}

struct Walk<'a> {
    body: &'a TypedBody,
    /// The variables that are static where the walk is.
    statics: HashSet<LocalId>,
    /// The variables that `var` binds.
    vars: HashSet<LocalId>,
    errors: Vec<Diagnostic>,
}

impl Walk<'_> {
    fn block(&mut self, b: &Block) {
        for s in b {
            if let StmtKind::Var(binding) = &s.kind {
                let mut bound = Vec::new();
                bound_by(&binding.pattern, &mut bound);
                self.vars.extend(bound);
            }
            for e in stmt_exprs(s) {
                self.expr(e);
            }
            // A variable that a `let` binds from a static value is static
            // (meta.static-expressions).
            if let StmtKind::Let(binding) = &s.kind
                && binding.otherwise.is_none()
                && self.first_dynamic(&binding.value).is_none()
            {
                let mut bound = Vec::new();
                bound_by(&binding.pattern, &mut bound);
                self.statics.extend(bound);
            }
        }
    }

    fn expr(&mut self, e: &Expr) {
        // The annotation is deleted with the space after it, which leaves the erased form.
        if let Some(keyword) = self.staged(e) {
            let annotation = TextRange::new(keyword.start(), e.at.start().max(keyword.end()));
            return self.annotated(e, annotation);
        }
        for p in parts(e) {
            match p {
                Part::Expr(e) => self.expr(e),
                Part::Block(b) => self.block(b),
            }
        }
    }

    /// Where the `comptime` that marks `e` is, if one does.
    fn staged(&self, e: &Expr) -> Option<TextRange> {
        let is_form = matches!(
            e.kind,
            ExprKind::If(..) | ExprKind::IfLet(..) | ExprKind::Match(..) | ExprKind::For(..)
        );
        is_form
            .then(|| self.body.staged.iter().find(|(_, form)| *form == e.at))
            .flatten()
            .map(|(keyword, _)| *keyword)
    }

    /// An annotated form: each of its annotated parts is checked, and its variables are static
    /// in the body, branch or arm they bind for.
    fn annotated(&mut self, e: &Expr, keyword: TextRange) {
        match &e.kind {
            ExprKind::For(pattern, iterable, b) => {
                match &**iterable {
                    Iterable::Iter(source) => self.require(source, "loop's iterable", keyword),
                    Iterable::Range(a, z, _) => {
                        let range = TextRange::new(a.at.start(), z.at.end());
                        self.require_all(&[a, z], (range, "loop's range"), keyword);
                    }
                }
                self.with_bound(&[pattern], |w| w.block(b));
            }
            ExprKind::Match(scrutinee, arms) => {
                self.require(scrutinee, "scrutinee", keyword);
                for arm in arms {
                    self.arm(arm, keyword);
                }
            }
            _ => self.chain(e, keyword),
        }
    }

    /// The `if`s of a `comptime if`'s chain, each condition and scrutinee annotated.
    fn chain(&mut self, e: &Expr, keyword: TextRange) {
        match &e.kind {
            ExprKind::If(c, b, alt) => {
                self.require(c, "condition", keyword);
                self.block(b);
                self.rest_of_chain(alt.as_deref(), keyword);
            }
            ExprKind::IfLet(pattern, scrutinee, b, alt) => {
                self.require(scrutinee, "scrutinee", keyword);
                self.with_bound(&[pattern], |w| w.block(b));
                self.rest_of_chain(alt.as_deref(), keyword);
            }
            _ => self.expr(e),
        }
    }

    fn rest_of_chain(&mut self, alt: Option<&Expr>, keyword: TextRange) {
        match alt {
            Some(
                next @ Expr {
                    kind: ExprKind::If(..) | ExprKind::IfLet(..),
                    ..
                },
            ) => self.chain(next, keyword),
            Some(other) => self.expr(other),
            None => {}
        }
    }

    /// An arm of a `comptime match`, whose guard is annotated and whose pattern's variables
    /// are static in the arm.
    fn arm(&mut self, arm: &Arm, keyword: TextRange) {
        self.with_bound(&[&arm.pattern], |w| {
            if let Some(guard) = &arm.guard {
                w.require(guard, "guard", keyword);
            }
            w.expr(&arm.body);
        });
    }

    /// Runs `f` with the variables of `patterns` static.
    fn with_bound(&mut self, patterns: &[&crate::tast::Pat], f: impl FnOnce(&mut Self)) {
        let mut bound = Vec::new();
        for p in patterns {
            bound_by(p, &mut bound);
        }
        let added: Vec<LocalId> = bound
            .into_iter()
            .filter(|v| self.statics.insert(*v))
            .collect();
        f(self);
        for v in added {
            self.statics.remove(&v);
        }
    }

    /// E0349 at the first part of `e` that isn't static, if there is one.
    fn require(&mut self, e: &Expr, part: &str, keyword: TextRange) {
        if let Some((at, reason)) = self.first_dynamic(e) {
            self.report(at, &reason, part, keyword);
        }
        self.expr(e);
    }

    /// One annotated part made of several expressions, as a range's bounds are.
    fn require_all(&mut self, es: &[&Expr], (_, part): (TextRange, &str), keyword: TextRange) {
        if let Some((at, reason)) = es.iter().find_map(|e| self.first_dynamic(e)) {
            self.report(at, &reason, part, keyword);
        }
        for e in es {
            self.expr(e);
        }
    }

    fn report(&mut self, at: TextRange, reason: &Reason, part: &str, keyword: TextRange) {
        let why = match reason {
            Reason::Param(n) => format!("`{n}` is a parameter, known only at run time"),
            Reason::Var(n) => format!("`{n}` is a `var`, which may change"),
            Reason::Bound(n) => format!("`{n}` is bound to a value known only at run time"),
            Reason::Performs => "this call performs the effects of its row".to_owned(),
            Reason::Runs(form) => format!("{form} runs code"),
        };
        let message =
            format!("`comptime` asserts that this {part} is known at compile time, but {why}");
        let fix = Fix::new(
            "delete `comptime`, which changes nothing the program does",
            vec![Edit::delete(keyword)],
        );
        self.errors
            .push(Diagnostic::new(codes::E0349, at, message).with_fix(fix));
    }
}

impl Walk<'_> {
    /// The first part of `e` that isn't static, in evaluation order, with why (meta.not-static): an
    /// expression's operands, callee, receiver and arguments come before it.
    fn first_dynamic(&self, e: &Expr) -> Option<(TextRange, Reason)> {
        let all = |es: &mut dyn Iterator<Item = &Expr>| {
            for e in es {
                if let Some(found) = self.first_dynamic(e) {
                    return Some(found);
                }
            }
            None
        };
        match &e.kind {
            ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Str(_)
            | ExprKind::Bool(_)
            | ExprKind::Constant(_)
            | ExprKind::MemberConstant(..)
            | ExprKind::ValueParam(_)
            // meta.static-reflection: a type's shape and name, and a bound test, are static.
            | ExprKind::Reflect(..)
            | ExprKind::Bound(..)
            | ExprKind::Hole
            | ExprKind::Error => None,
            ExprKind::Local(v) => self.local(*v, e.at),
            ExprKind::Interpolated(segments) => all(&mut segments.iter().filter_map(|s| match s {
                Segment::Splice(e, _) => Some(&**e),
                Segment::Text(_) => None,
            })),
            ExprKind::Tuple(es) | ExprKind::List(es) | ExprKind::Construct(_, _, es) => {
                all(&mut es.iter())
            }
            ExprKind::Record(_, _, fields) => all(&mut fields.iter().map(|(_, e)| e)),
            ExprKind::Update(base, fields) => {
                all(&mut std::iter::once(&**base).chain(fields.iter().map(|(_, e)| e)))
            }
            ExprKind::Field(base, _) | ExprKind::TupleField(base, _) | ExprKind::Unary(_, base) => {
                self.first_dynamic(base)
            }
            ExprKind::Index(a, b) | ExprKind::Binary(_, a, b) => all(&mut [&**a, &**b].into_iter()),
            ExprKind::Call(callee, _, args, row) | ExprKind::Project(callee, _, args, row) => {
                all(&mut args.iter().map(|a| &a.value)).or_else(|| {
                    let performs = !row.is_empty() || matches!(callee, Callee::Operation(..));
                    performs.then_some((e.at, Reason::Performs))
                })
            }
            ExprKind::CallValue(f, args) => {
                all(&mut std::iter::once(&**f).chain(args.iter().map(|a| &a.value))).or(Some((
                    e.at,
                    Reason::Runs("a call through a function value"),
                )))
            }
            _ => Some((e.at, Reason::Runs(runs(e)))),
        }
    }

    fn local(&self, v: LocalId, at: TextRange) -> Option<(TextRange, Reason)> {
        if self.statics.contains(&v) {
            return None;
        }
        let name = self.body.locals[v.0 as usize].to_string();
        let reason = if self.body.params.iter().any(|(_, p)| *p == v) {
            Reason::Param(name)
        } else if self.vars.contains(&v) {
            Reason::Var(name)
        } else {
            Reason::Bound(name)
        };
        Some((at, reason))
    }
}

/// The form an expression that runs code is, as E0349 names it: a block, a branch, a loop, a
/// closure and the others are reported whole (meta.not-static).
fn runs(e: &Expr) -> &'static str {
    match &e.kind {
        ExprKind::Block(_) => "a block",
        ExprKind::If(..) | ExprKind::IfLet(..) => "an `if`",
        ExprKind::Match(..) => "a `match`",
        ExprKind::Loop(_) | ExprKind::While(..) | ExprKind::For(..) => "a loop",
        ExprKind::Closure(..) => "a closure",
        ExprKind::Try(..) => "a `try`",
        ExprKind::Else(..) => "an `else`",
        ExprKind::Callee(..) | ExprKind::Constructor(..) | ExprKind::Instantiate(..) => {
            "a function value"
        }
        _ => "this expression",
    }
}
