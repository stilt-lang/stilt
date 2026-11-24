//! Typed code with every type and row replaced: by its solution, when inference freezes a body
//! into the form that the later phases read, and by its instance, when the backend compiles a
//! body for the constructors its key knows.

use crate::tast::{
    Arm, Block, Callee, Code, Expr, ExprKind, Iterable, Pat, PatKind, Segment, StmtKind,
};
use crate::ty::{Row, Table, Ty};
use stilt_hir::hir::fit;

/// A replacement of every type and row of typed code.
pub struct Retype<'f> {
    /// The replacement of a type.
    pub ty: &'f dyn Fn(&Ty) -> Ty,
    /// The replacement of a row.
    pub row: &'f dyn Fn(&Row) -> Row,
    /// Whether the bodies of spreads are retyped too (variadics.spread-expressions).
    pub spreads: bool,
}

impl std::fmt::Debug for Retype<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Retype").finish_non_exhaustive()
    }
}

/// Freezes typed code: each variable replaced by its solution, and each row by what it holds.
pub(crate) fn freeze(table: &Table, code: impl FnOnce(&Retype<'_>) -> Code) -> Code {
    let ty = |t: &Ty| table.freeze(t);
    let row = |r: &Row| table.freeze_row(r);
    code(&Retype {
        ty: &ty,
        row: &row,
        spreads: true,
    })
}

impl Retype<'_> {
    fn ty(&self, t: &mut Ty) {
        *t = (self.ty)(t);
    }

    /// Replaces the types of a body's code.
    pub fn code(&self, code: &mut Code) {
        match code {
            Code::Block(b) => self.block(b),
            Code::Expr(e) => self.expr(e),
        }
    }

    fn tys(&self, ts: &mut Vec<Ty>) {
        fit(ts);
        for t in ts {
            self.ty(t);
        }
    }

    fn exprs<'e>(&self, es: impl IntoIterator<Item = &'e mut Expr>) {
        for e in es {
            self.expr(e);
        }
    }

    fn callee(&self, c: &mut Callee, targs: &mut Vec<Ty>) {
        if let Callee::TraitMethod(_, _, t) = c {
            self.ty(t);
        }
        self.tys(targs);
    }

    /// Retypes an expression and every part of it.
    pub fn expr(&self, e: &mut Expr) {
        self.ty(&mut e.ty);
        match &mut e.kind {
            ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Str(_)
            | ExprKind::Bool(_)
            | ExprKind::Local(_)
            | ExprKind::Constant(_)
            | ExprKind::ValueParam(_)
            | ExprKind::Hole
            | ExprKind::Error
            | ExprKind::Break
            | ExprKind::Continue => {}
            ExprKind::Interpolated(segments) => self.segments(segments),
            ExprKind::MemberConstant(_, _, ts) | ExprKind::Constructor(_, ts) => self.tys(ts),
            ExprKind::Reflect(..) | ExprKind::Bound(..) => self.reflection(&mut e.kind),
            ExprKind::Callee(c, ts) => self.callee(c, ts),
            ExprKind::Construct(_, ts, es) => {
                self.tys(ts);
                fit(es);
                self.exprs(es);
            }
            ExprKind::Record(_, ts, fields) => {
                self.tys(ts);
                fit(fields);
                self.exprs(fields.iter_mut().map(|(_, e)| e));
            }
            ExprKind::Tuple(es) | ExprKind::List(es) => {
                fit(es);
                self.exprs(es);
            }
            ExprKind::Field(e, _)
            | ExprKind::TupleField(e, _)
            | ExprKind::Unary(_, e)
            | ExprKind::Raise(e) => self.expr(e),
            ExprKind::Call(c, ts, args, row) | ExprKind::Project(c, ts, args, row) => {
                self.callee(c, ts);
                fit(args);
                self.exprs(args.iter_mut().map(|a| &mut a.value));
                *row = (self.row)(row);
            }
            ExprKind::CallValue(f, args) => {
                self.expr(f);
                fit(args);
                self.exprs(args.iter_mut().map(|a| &mut a.value));
            }
            ExprKind::Instantiate(f, ts) => {
                self.expr(f);
                self.tys(ts);
            }
            ExprKind::Index(a, b) | ExprKind::Binary(_, a, b) | ExprKind::Else(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ExprKind::Return(e) | ExprKind::Resume(e) => {
                self.exprs(e.iter_mut().map(|e| &mut **e));
            }
            kind => self.control(kind),
        }
    }

    /// `T.shape()`, `T.name()` and a bound test, which name a type (meta.shape-and-name and
    /// meta.bound-tests).
    fn reflection(&self, kind: &mut ExprKind) {
        match kind {
            ExprKind::Reflect(_, t) => self.ty(t),
            ExprKind::Bound(t, traits) => {
                self.ty(t);
                for (_, args) in traits {
                    self.tys(args);
                }
            }
            _ => {}
        }
    }

    /// The forms that hold blocks, arms or patterns, and updates and spreads.
    fn control(&self, kind: &mut ExprKind) {
        match kind {
            ExprKind::Update(base, fields) => {
                self.expr(base);
                fit(fields);
                self.exprs(fields.iter_mut().map(|(_, e)| e));
            }
            // A spread's body names its pack's element, which stands for each element in turn,
            // so a retyping that replaces the pack leaves the body to the code that maps it.
            ExprKind::Spread(s) => {
                self.ty(&mut s.pack);
                if self.spreads {
                    self.expr(&mut s.body);
                }
            }
            ExprKind::Try(operand, catch) => {
                self.expr(operand);
                if let Some(c) = catch {
                    self.ty(&mut c.error);
                    self.arms(&mut c.arms);
                }
            }
            ExprKind::Closure(params, body) => {
                fit(params);
                for p in params {
                    self.pat(p);
                }
                self.expr(body);
            }
            ExprKind::Block(b) | ExprKind::Loop(b) => self.block(b),
            ExprKind::If(cond, b, alt) => {
                self.expr(cond);
                self.block(b);
                self.exprs(alt.iter_mut().map(|e| &mut **e));
            }
            ExprKind::IfLet(pattern, scrutinee, b, alt) => {
                self.pat(pattern);
                self.expr(scrutinee);
                self.block(b);
                self.exprs(alt.iter_mut().map(|e| &mut **e));
            }
            ExprKind::Match(scrutinee, arms) => {
                self.expr(scrutinee);
                self.arms(arms);
            }
            ExprKind::While(cond, b) => {
                self.expr(cond);
                self.block(b);
            }
            ExprKind::For(target, iterable, b) => {
                self.pat(target);
                match &mut **iterable {
                    Iterable::Iter(source) => self.expr(source),
                    Iterable::Range(from, to, _) => {
                        self.expr(from);
                        self.expr(to);
                    }
                }
                self.block(b);
            }
            _ => self.handling(kind),
        }
    }

    /// A handler literal and a `with` (handlers.handler-literals and handlers.with).
    fn handling(&self, kind: &mut ExprKind) {
        match kind {
            ExprKind::Handler(h) => {
                fit(&mut h.ops);
                self.exprs(h.ops.iter_mut().map(|(_, e)| e));
            }
            ExprKind::With(h, _, ts, b) => {
                self.expr(h);
                self.tys(ts);
                self.block(b);
            }
            ExprKind::When(held, b) => {
                fit(held);
                for (h, _) in held {
                    self.expr(h);
                }
                self.block(b);
            }
            ExprKind::Quote(q) => {
                fit(&mut q.splices);
                for s in &mut q.splices {
                    self.expr(&mut s.value);
                }
            }
            _ => unreachable!("`expr` freezes the other forms"),
        }
    }

    fn segments(&self, segments: &mut Vec<Segment>) {
        fit(segments);
        for s in segments {
            if let Segment::Splice(e, _) = s {
                self.expr(e);
            }
        }
    }

    fn arms(&self, arms: &mut Vec<Arm>) {
        fit(arms);
        for a in arms {
            self.pat(&mut a.pattern);
            self.exprs(a.guard.as_deref_mut());
            self.expr(&mut a.body);
        }
    }

    /// Retypes each statement of a block.
    pub fn block(&self, b: &mut Block) {
        fit(b);
        for s in b {
            match &mut s.kind {
                StmtKind::Let(binding) | StmtKind::Var(binding) => {
                    self.pat(&mut binding.pattern);
                    self.expr(&mut binding.value);
                    self.exprs(binding.otherwise.as_deref_mut());
                }
                StmtKind::Assign(_, place, value) => {
                    self.expr(place);
                    self.expr(value);
                }
                StmtKind::Assert(e) | StmtKind::Yield(e) | StmtKind::Expr(e) => self.expr(e),
            }
        }
    }

    fn pat(&self, p: &mut Pat) {
        self.ty(&mut p.ty);
        match &mut p.kind {
            PatKind::Tuple(ps)
            | PatKind::Variant(_, ps)
            | PatKind::List(ps, _)
            | PatKind::Or(ps) => {
                fit(ps);
                for q in ps {
                    self.pat(q);
                }
            }
            PatKind::Const(e) => self.expr(e),
            PatKind::Record(fields) => {
                fit(fields);
                for (_, q) in fields {
                    self.pat(q);
                }
            }
            PatKind::Wild
            | PatKind::Bind(_)
            | PatKind::Int(_)
            | PatKind::Str(_)
            | PatKind::Bool(_)
            | PatKind::Error => {}
        }
    }
}
