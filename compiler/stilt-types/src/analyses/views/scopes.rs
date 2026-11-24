//! Views that outlive a scope inside a function (views.escaping): a view may leave the scope
//! that binds one of its sources nowhere, so the value of a block that views a binding the
//! block makes, the value of a `match`, `if let` or `catch` arm that views a binding of its
//! pattern, the value of a `for` body that views a binding of the loop, and the value of a `when`
//! that views a name it holds, are E0422, at the
//! expression that gives the scope its value, naming the binding, and so is a view assigned to
//! a variable bound outside the scope of one of its sources, at the value assigned. A closure that
//! captures such a view carries it out too. An expression that leaves several scopes is
//! reported once, for the innermost. The function's own block gives its result, which
//! [`super::escapes`] checks.

use stilt_diag::{Diagnostic, codes};
use stilt_hir::hir::{LocalId, Name};

use super::super::modes::places::place;
use super::Sources;
use super::sources::bound_by;
use crate::tast::walk::{self, Part};
use crate::tast::{Arm, Block, Expr, ExprKind, Pat, StmtKind};
use crate::ty::Ty;

/// The scope whose value a view would leave.
#[derive(Clone, Copy)]
enum Scope {
    Block,
    Arm,
    Loop,
    Held,
}

struct Scopes<'a> {
    found: &'a Sources,
    locals: &'a [Name],
    /// The bindings of each scope around the code being checked, innermost last.
    stack: Vec<Vec<LocalId>>,
    errors: Vec<Diagnostic>,
}

/// The errors of views.escaping at the scopes inside a function's block, `block`.
pub(super) fn errors(locals: &[Name], block: &Block, found: &Sources) -> Vec<Diagnostic> {
    let mut s = Scopes {
        found,
        locals,
        stack: vec![lets(block, Vec::new())],
        errors: Vec::new(),
    };
    s.statements(block);
    let mut errors: Vec<Diagnostic> = Vec::new();
    for d in s.errors {
        if !errors.iter().any(|e| e.range == d.range) {
            errors.push(d);
        }
    }
    errors
}

/// The variables that a pattern binds.
fn bound(p: &Pat) -> Vec<LocalId> {
    let mut vars = Vec::new();
    bound_by(p, &mut vars);
    vars
}

/// `more` and the variables that a block's statements bind.
fn lets(b: &Block, mut more: Vec<LocalId>) -> Vec<LocalId> {
    for s in b {
        if let StmtKind::Let(x) | StmtKind::Var(x) = &s.kind {
            bound_by(&x.pattern, &mut more);
        }
    }
    more
}

/// Whether a value may carry a view: a view type, or a closure, which may capture one.
fn may_view(e: &Expr) -> bool {
    e.ty.is_view() || matches!(e.ty, Ty::Fn(_))
}

impl Scopes<'_> {
    /// Checks the code of a block's statements, and the views they assign.
    fn statements(&mut self, b: &Block) {
        for s in b {
            for e in walk::stmt_exprs(s) {
                self.expr(e);
            }
            if let StmtKind::Assign(None, target, value) = &s.kind {
                self.assigned(target, value);
            }
        }
    }

    /// Checks a block's code, then its value against the bindings its statements make and
    /// `more`, the bindings of the pattern it is the body of.
    fn block(&mut self, b: &Block, more: Vec<LocalId>, scope: Scope) {
        self.stack.push(lets(b, more));
        self.statements(b);
        let vars = self.stack.pop().unwrap_or_default();
        if let Some(StmtKind::Expr(tail)) = b.last().map(|s| &s.kind) {
            self.value(tail, &vars, scope);
        }
    }

    /// Checks an arm's code, then its value against the bindings of its pattern.
    fn arm(&mut self, a: &Arm) {
        let vars = bound(&a.pattern);
        self.stack.push(vars);
        if let Some(g) = &a.guard {
            self.expr(g);
        }
        self.expr(&a.body);
        let vars = self.stack.pop().unwrap_or_default();
        self.value(&a.body, &vars, Scope::Arm);
    }

    /// The depth of the scope that binds `v`, if one inside the function does.
    fn depth(&self, v: LocalId) -> Option<usize> {
        self.stack.iter().rposition(|vars| vars.contains(&v))
    }

    /// E0422 at a view assigned to `target`, a variable bound outside the scope of one of the
    /// view's sources, which ends first.
    fn assigned(&mut self, target: &Expr, value: &Expr) {
        let Some(held) = place(target).and_then(|p| self.depth(p.root)) else {
            return;
        };
        if !may_view(value) {
            return;
        }
        let sources = self.found.places(value);
        let Some(source) = sources
            .iter()
            .find(|p| self.depth(p.root).is_some_and(|d| d > held))
        else {
            return;
        };
        let what = if matches!(value.ty, Ty::Fn(_)) {
            "this closure"
        } else {
            "this view"
        };
        let name = source.name(self.locals);
        let to = &self.locals[place(target).map_or(0, |p| p.root.0 as usize)];
        let message =
            format!("{what} is assigned to `{to}`, but it views `{name}`, which ends first");
        self.errors
            .push(Diagnostic::new(codes::E0422, value.at, message));
    }

    /// Checks the scopes inside an expression.
    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Match(scrutinee, arms) => {
                self.expr(scrutinee);
                for a in arms {
                    self.arm(a);
                }
            }
            ExprKind::Try(operand, catch) => {
                self.expr(operand);
                for a in walk::catch_arms(catch.as_ref()) {
                    self.arm(a);
                }
            }
            ExprKind::IfLet(p, scrutinee, b, alt) => {
                self.expr(scrutinee);
                self.block(b, bound(p), Scope::Arm);
                if let Some(a) = alt {
                    self.expr(a);
                }
            }
            // shared.when: the names a `when` holds stand for the places of the values it
            // holds, which it releases when its block ends.
            ExprKind::When(names, b) => {
                for (handle, _) in names {
                    self.expr(handle);
                }
                let held = names.iter().map(|(_, v)| *v).collect();
                self.block(b, held, Scope::Held);
            }
            ExprKind::For(p, _, b) => {
                for part in walk::parts(e) {
                    if let Part::Expr(x) = part {
                        self.expr(x);
                    }
                }
                self.block(b, bound(p), Scope::Loop);
            }
            _ => {
                for part in walk::parts(e) {
                    match part {
                        Part::Expr(x) => self.expr(x),
                        Part::Block(b) => self.block(b, Vec::new(), Scope::Block),
                    }
                }
            }
        }
    }

    /// E0422 at each expression that gives `e` its value, through its blocks and branches, and
    /// views one of `vars`, which end with the scope.
    fn value(&mut self, e: &Expr, vars: &[LocalId], scope: Scope) {
        if vars.is_empty() {
            return;
        }
        let mut leaves = Vec::new();
        leaves_of(e, &mut leaves);
        for leaf in leaves {
            if !may_view(leaf) {
                continue;
            }
            let sources = self.found.places(leaf);
            if let Some(source) = sources.iter().find(|p| vars.contains(&p.root)) {
                let d = self.escape(leaf, source.name(self.locals), scope);
                self.errors.push(d);
            }
        }
    }

    /// E0422 at `leaf`, which views `name` out of the scope that binds it.
    fn escape(&self, leaf: &Expr, name: &str, scope: Scope) -> Diagnostic {
        let what = if matches!(leaf.ty, Ty::Fn(_)) {
            "this closure"
        } else {
            "this view"
        };
        let (of, binds) = match scope {
            Scope::Block => ("its block's value", "which the block binds"),
            Scope::Arm => ("its arm's value", "which the arm's pattern binds"),
            Scope::Loop => ("the loop body's value", "which the loop binds"),
            Scope::Held => ("the `when`'s value", "which the `when` holds"),
        };
        let message = format!("{what} is {of}, but it views `{name}`, {binds}");
        let mut d = Diagnostic::new(codes::E0422, leaf.at, message);
        if let ExprKind::Local(v) = leaf.kind
            && let Some(at) = self.found.binding_at(v)
        {
            let held = &self.locals[v.0 as usize];
            d = d.with_note(at, format!("`{held}` views `{name}` from here"));
        }
        d
    }
}

/// The expressions that give the value of `e`, through its blocks and branches.
fn leaves_of<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    let tail = |b: &'a Block, out: &mut Vec<&'a Expr>| {
        if let Some(StmtKind::Expr(x)) = b.last().map(|s| &s.kind) {
            leaves_of(x, out);
        }
    };
    match &e.kind {
        ExprKind::Block(b) => tail(b, out),
        ExprKind::If(_, b, alt) | ExprKind::IfLet(_, _, b, alt) => {
            tail(b, out);
            if let Some(a) = alt {
                leaves_of(a, out);
            }
        }
        ExprKind::Match(_, arms) => {
            for a in arms {
                leaves_of(&a.body, out);
            }
        }
        ExprKind::Else(a, b) => {
            leaves_of(a, out);
            leaves_of(b, out);
        }
        _ => out.push(e),
    }
}
