//! The holes of a typed body, each with the bindings in scope where it stands and the closure
//! around it whose type bounds its effects (goal hole-context).

use stilt_hir::hir::{ListRest, LocalId, Name};
use stilt_syntax::TextRange;

use crate::tast::walk::{Part, catch_arms, parts};
use crate::tast::{Arg, Arm, Block, Code, Expr, ExprKind, Iterable, Pat, PatKind, Stmt, StmtKind};
use crate::ty::{Row, Ty};

/// A hole of a body.
pub(super) struct Site {
    /// Where it is, relative to the body's start.
    pub(super) at: TextRange,
    /// The type its context expects.
    pub(super) ty: Ty,
    /// The bindings in scope where it stands, in the order they are bound.
    pub(super) scope: Vec<Binding>,
    /// The row of the innermost closure around it that an escaping parameter takes, whose type
    /// then bounds what the hole may perform. Any other closure passes through what the code
    /// around it may perform.
    pub(super) row: Option<Row>,
}

/// A binding in scope.
#[derive(Clone)]
pub(super) struct Binding {
    pub(super) name: Name,
    pub(super) ty: Ty,
    /// Whether code may pass it `inout`: a `var`'s, or an `inout` parameter's
    /// (modes.what-can-be-modified).
    pub(super) mutable: bool,
}

/// The holes of `code`, in the order they are written, where the body's parameters `params`
/// are in scope, and `locals` names the body's variables.
pub(super) fn sites(params: Vec<Binding>, locals: &[Name], code: &Code) -> Vec<Site> {
    let mut walker = Walker {
        locals,
        scope: params,
        mutable: false,
        row: None,
        found: Vec::new(),
    };
    match code {
        Code::Block(b) => walker.block(b),
        Code::Expr(e) => walker.expr(e),
    }
    walker.found
}

struct Walker<'l> {
    locals: &'l [Name],
    scope: Vec<Binding>,
    /// Whether the pattern being bound is a `var`'s.
    mutable: bool,
    row: Option<Row>,
    found: Vec<Site>,
}

impl Walker<'_> {
    /// Walks `inside` with the bindings it adds to the scope dropped after it.
    fn scoped(&mut self, inside: impl FnOnce(&mut Self)) {
        let mark = self.scope.len();
        inside(self);
        self.scope.truncate(mark);
    }

    fn block(&mut self, b: &Block) {
        self.scoped(|w| b.iter().for_each(|s| w.stmt(s)));
    }

    /// A statement, whose `let` or `var` binds its pattern for the statements after it: its
    /// value and its `else` don't see it.
    fn stmt(&mut self, s: &Stmt) {
        match &s.kind {
            StmtKind::Let(b) | StmtKind::Var(b) => {
                self.expr(&b.value);
                if let Some(otherwise) = &b.otherwise {
                    self.expr(otherwise);
                }
                self.mutable = matches!(s.kind, StmtKind::Var(_));
                self.bind(&b.pattern);
                self.mutable = false;
            }
            StmtKind::Assign(_, place, value) => {
                self.expr(place);
                self.expr(value);
            }
            StmtKind::Assert(e) | StmtKind::Yield(e) | StmtKind::Expr(e) => self.expr(e),
        }
    }

    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Hole => self.found.push(Site {
                at: e.at,
                ty: e.ty.clone(),
                scope: self.scope.clone(),
                row: self.row.clone(),
            }),
            ExprKind::Closure(params, body) => self.closure(params, body, None),
            ExprKind::Call(_, _, args, _) | ExprKind::Project(_, _, args, _) => self.args(args),
            ExprKind::CallValue(f, args) => {
                self.expr(f);
                self.args(args);
            }
            ExprKind::Match(scrutinee, arms) => {
                self.expr(scrutinee);
                for a in arms {
                    self.arm(a);
                }
            }
            ExprKind::Try(tried, catch) => {
                self.expr(tried);
                for a in catch_arms(catch.as_ref()) {
                    self.arm(a);
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
            _ => {
                for part in parts(e) {
                    match part {
                        Part::Expr(x) => self.expr(x),
                        Part::Block(b) => self.block(b),
                    }
                }
            }
        }
    }

    /// A call's arguments. A closure that an escaping parameter takes may perform only what its
    /// type holds; one that a non-escaping parameter takes passes its effects through to the
    /// call (effects.non-escaping-parameters and effects.escaping-parameters).
    fn args(&mut self, args: &[Arg]) {
        for a in args {
            match &a.value.kind {
                ExprKind::Closure(params, body) if !a.passes => {
                    let row = match &a.value.ty {
                        Ty::Fn(f) => Some(f.row.clone()),
                        _ => None,
                    };
                    self.closure(params, body, row);
                }
                _ => self.expr(&a.value),
            }
        }
    }

    /// A closure, whose parameters are in scope in its body, and whose holes may perform what
    /// `row` holds if it is given.
    fn closure(&mut self, params: &[Pat], body: &Expr, row: Option<Row>) {
        let outer = self.row.clone();
        if row.is_some() {
            self.row = row;
        }
        self.scoped(|w| {
            for p in params {
                w.bind(p);
            }
            w.expr(body);
        });
        self.row = outer;
    }

    fn arm(&mut self, a: &Arm) {
        self.scoped(|w| {
            w.bind(&a.pattern);
            if let Some(guard) = &a.guard {
                w.expr(guard);
            }
            w.expr(&a.body);
        });
    }

    fn push(&mut self, v: LocalId, ty: &Ty) {
        if let Some(name) = self.locals.get(v.0 as usize) {
            self.scope.push(Binding {
                name: *name,
                ty: ty.clone(),
                mutable: self.mutable,
            });
        }
    }

    /// Adds the variables that `p` binds to the scope. Each alternative of an or-pattern binds
    /// the same names (patterns.or-patterns), so the first one's stand for all.
    fn bind(&mut self, p: &Pat) {
        match &p.kind {
            PatKind::Bind(v) => self.push(*v, &p.ty),
            PatKind::Tuple(ps) | PatKind::Variant(_, ps) => ps.iter().for_each(|q| self.bind(q)),
            PatKind::Record(fields) => fields.iter().for_each(|(_, q)| self.bind(q)),
            PatKind::List(ps, rest) => {
                for q in ps {
                    self.bind(q);
                }
                if let ListRest::Bind(v) = rest {
                    self.push(*v, &p.ty);
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
            | PatKind::Error => {}
        }
    }
}
