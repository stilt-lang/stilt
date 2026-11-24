//! Positions in a body relative to the body's start, so that an edit that only moves a body leaves
//! it as it was, and the queries that read it don't run again (goal body-edits-recheck-one-body);
//! and the positions of a macro's expansion moved to the tokens the user wrote
//! (macros.errors-in-expansions), by the same walk.

use stilt_diag::Diagnostic;
use stilt_syntax::{TextRange, TextSize};

use super::{
    Arm, Block, Body, BodyValue, ClosureParam, Expr, ExprKind, Ident, Iterable, MemberOwner, Pat,
    PatKind, Segment, StmtKind, TypeRef,
};

/// Moves every position of a body back by `origin`.
pub(crate) fn rebase(body: &mut Body, origin: TextSize) {
    // A position before the body's start is that of a part missing from the tree, which a body
    // with a syntax error has, and which nothing reports.
    let back = |at: TextRange| {
        let offset = |at: TextSize| at.checked_sub(origin).unwrap_or_default();
        TextRange::new(offset(at.start()), offset(at.end()))
    };
    let r = Rebase(&back);
    super::fit(&mut body.locals);
    super::fit(&mut body.params);
    for e in &mut body.expansions {
        r.range(&mut e.at);
    }
    for u in &mut body.unsafe_blocks {
        r.range(&mut u.at);
        r.range(&mut u.whole);
    }
    r.range(&mut body.at);
    for local in &mut body.locals {
        r.range(&mut local.at);
    }
    for (_, at) in &mut body.limits {
        r.range(at);
    }
    for (_, _, _, at) in &mut body.fixed {
        r.range(at);
    }
    for (_, d) in &mut body.held {
        r.diagnostic(d);
    }
    for d in &mut body.analysed {
        r.diagnostic(d);
    }
    if let Some(s) = &mut body.signature {
        for (_, at, _) in &mut s.generics {
            *at = r.offset(*at);
        }
        s.generics_at = r.offset(s.generics_at);
        s.end = r.offset(s.end);
        for p in std::iter::once(&mut s.row).chain(s.params.iter_mut().flatten()) {
            p.row_at = r.offset(p.row_at);
            p.wrap = p.wrap.map(|at| r.offset(at));
            if let Some((at, _)) = &mut p.row {
                r.range(at);
            }
        }
    }
    match &mut body.value {
        BodyValue::Block(block) => r.block(block),
        BodyValue::Expr(e) | BodyValue::Property(e, _) => r.expr(e),
    }
}

/// Moves every position of an expression by `map`.
pub(crate) fn remap_expr(e: &mut Expr, map: &dyn Fn(TextRange) -> TextRange) {
    Rebase(map).expr(e);
}

/// Moves every position of a pattern by `map`.
pub(crate) fn remap_pat(p: &mut Pat, map: &dyn Fn(TextRange) -> TextRange) {
    Rebase(map).pat(p);
}

/// Moves every position of a diagnostic by `map`, but for the notes given in the file's
/// positions.
pub(crate) fn remap_diagnostic(d: &mut Diagnostic, map: &dyn Fn(TextRange) -> TextRange) {
    Rebase(map).diagnostic(d);
}

/// The walk that moves every position by a map.
struct Rebase<'m>(&'m dyn Fn(TextRange) -> TextRange);

impl Rebase<'_> {
    fn range(&self, at: &mut TextRange) {
        *at = (self.0)(*at);
    }

    fn offset(&self, at: TextSize) -> TextSize {
        (self.0)(TextRange::empty(at)).start()
    }

    fn ident(&self, n: &mut Ident) {
        self.range(&mut n.at);
    }

    /// A diagnostic of the body, but for the notes already given in the file's positions.
    fn diagnostic(&self, d: &mut Diagnostic) {
        self.range(&mut d.range);
        for note in d.notes.iter_mut().filter(|n| !n.in_file) {
            self.range(&mut note.range);
        }
        for edit in d.fixes.iter_mut().flat_map(|fix| &mut fix.edits) {
            self.range(&mut edit.range);
        }
    }

    fn ty(&self, t: &mut TypeRef) {
        self.range(&mut t.at);
    }

    fn block(&self, block: &mut Block) {
        super::fit(block);
        for stmt in block {
            self.range(&mut stmt.at);
            match &mut stmt.kind {
                StmtKind::Let(b) | StmtKind::Var(b) => {
                    self.pat(&mut b.pattern);
                    if let Some(t) = &mut b.annotation {
                        self.ty(t);
                    }
                    self.expr(&mut b.value);
                }
                StmtKind::Assign(_, place, value) => {
                    self.expr(place);
                    self.expr(value);
                }
                StmtKind::Assert(e) | StmtKind::Yield(e) | StmtKind::Expr(e) => self.expr(e),
            }
        }
    }

    fn exprs<'e>(&self, es: impl IntoIterator<Item = &'e mut Expr>) {
        for e in es {
            self.expr(e);
        }
    }

    fn expr(&self, e: &mut Expr) {
        self.range(&mut e.at);
        match &mut e.kind {
            ExprKind::Interpolated(segments) => {
                super::fit(segments);
                for segment in segments {
                    if let Segment::Splice(e, _) = segment {
                        self.expr(e);
                    }
                }
            }
            ExprKind::Member(owner, name) => {
                if let MemberOwner::Type(t) = owner {
                    self.ty(t);
                }
                self.ident(name);
            }
            ExprKind::Tuple(es) | ExprKind::List(es) => {
                super::fit(es);
                self.exprs(es);
            }
            ExprKind::Field(base, field) => {
                self.expr(base);
                self.ident(field);
            }
            ExprKind::Unary(_, e)
            | ExprKind::Spread(e)
            | ExprKind::Raise(e)
            | ExprKind::Return(Some(e)) => self.expr(e),
            ExprKind::Call(callee, args) => {
                self.expr(callee);
                super::fit(args);
                for a in args {
                    self.range(&mut a.at);
                    self.expr(&mut a.value);
                }
            }
            ExprKind::Index(a, b) | ExprKind::Binary(_, a, b) | ExprKind::Else(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ExprKind::Struct(t, fields) => {
                self.ty(t);
                self.field_inits(fields);
            }
            ExprKind::Update(t, base, fields) => {
                if let Some(t) = t {
                    self.ty(t);
                }
                self.expr(base);
                self.field_inits(fields);
            }
            ExprKind::Closure(params, body) => {
                super::fit(params);
                for p in params {
                    self.closure_param(p);
                }
                self.expr(body);
            }
            kind => self.control(kind),
        }
    }

    fn field_inits(&self, fields: &mut Vec<super::body::FieldInit>) {
        super::fit(fields);
        for f in fields {
            self.ident(&mut f.field);
            self.expr(&mut f.value);
        }
    }

    /// A bound test's type parameter and the bounds it names (meta.bound-tests).
    fn bound_test(&self, test: &mut super::BoundTest) {
        self.ident(&mut test.name);
        super::fit(&mut test.bounds);
        for (_, at) in &mut test.bounds {
            self.range(at);
        }
    }

    /// The forms that hold blocks or arms, and those that hold no positions but their own.
    fn control(&self, kind: &mut ExprKind) {
        match kind {
            ExprKind::Try(operand, arms) => {
                self.expr(operand);
                if let Some(arms) = arms {
                    super::fit(arms);
                }
                self.arms(arms.iter_mut().flatten());
            }
            ExprKind::Match(scrutinee, arms) => {
                self.expr(scrutinee);
                super::fit(arms);
                self.arms(arms);
            }
            ExprKind::Block(block) | ExprKind::Loop(block) => self.block(block),
            ExprKind::Comptime(form) => self.expr(form),
            ExprKind::If(cond, body, alt) => {
                self.expr(cond);
                self.block(body);
                self.exprs(alt.iter_mut().map(|e| &mut **e));
            }
            ExprKind::IfLet(pattern, scrutinee, body, alt) => {
                self.pat(pattern);
                self.expr(scrutinee);
                self.block(body);
                self.exprs(alt.iter_mut().map(|e| &mut **e));
            }
            ExprKind::While(cond, body) => {
                self.expr(cond);
                self.block(body);
            }
            ExprKind::For(pattern, iterable, body) => {
                self.pat(pattern);
                match &mut **iterable {
                    Iterable::Iter(e) => self.expr(e),
                    Iterable::Range(start, end, _) => {
                        self.expr(start);
                        self.expr(end);
                    }
                }
                self.block(body);
            }
            ExprKind::Perform(_, name) => self.ident(name),
            ExprKind::Bound(test) => self.bound_test(test),
            ExprKind::Quote(q) => self.quote(q),
            ExprKind::Handler(h) => self.handler(h),
            ExprKind::With(handlers, body) => {
                super::fit(handlers);
                self.exprs(handlers);
                self.block(body);
            }
            ExprKind::Resume(value) => self.exprs(value.iter_mut().map(|e| &mut **e)),
            ExprKind::When(held, body) => {
                super::fit(held);
                self.exprs(held.iter_mut().map(|h| &mut h.handle));
                self.block(body);
            }
            _ => {}
        }
    }

    /// A quote's positions: its splices' (macros.splices).
    fn quote(&self, q: &mut super::Quote) {
        super::fit(&mut q.tokens);
        super::fit(&mut q.splices);
        super::fit(&mut q.names);
        for s in &mut q.splices {
            self.range(&mut s.at);
            self.expr(&mut s.value);
        }
    }

    /// A handler literal's positions: its effect's, its answer's and its operations'
    /// (handlers.handler-literals).
    fn handler(&self, h: &mut super::HandlerLit) {
        self.range(&mut h.effect_at);
        if let Some(t) = &mut h.answer {
            self.ty(t);
        }
        super::fit(&mut h.ops);
        for op in &mut h.ops {
            self.ident(&mut op.name);
            super::fit(&mut op.params);
            for (_, _, t) in &mut op.params {
                self.ty(t);
            }
            if let Some(t) = &mut op.ret {
                self.ty(t);
            }
            self.block(&mut op.body);
        }
    }

    fn closure_param(&self, p: &mut ClosureParam) {
        self.range(&mut p.at);
        self.pat(&mut p.pattern);
        if let Some(t) = &mut p.annotation {
            self.ty(t);
        }
    }

    fn arms<'a>(&self, arms: impl IntoIterator<Item = &'a mut Arm>) {
        for arm in arms {
            self.pat(&mut arm.pattern);
            if let Some(guard) = &mut arm.guard {
                self.expr(guard);
            }
            if let Some((_, at)) = &mut arm.because {
                self.range(at);
            }
            self.expr(&mut arm.body);
        }
    }

    fn pat(&self, p: &mut Pat) {
        self.range(&mut p.at);
        match &mut p.kind {
            PatKind::Tuple(ps)
            | PatKind::Variant(_, ps)
            | PatKind::List(ps, _)
            | PatKind::Or(ps) => {
                super::fit(ps);
                for q in ps {
                    self.pat(q);
                }
            }
            PatKind::AssocConst(t, name) => {
                self.ty(t);
                self.ident(name);
            }
            PatKind::Bare(name, ps, _) => {
                self.ident(name);
                super::fit(ps);
                for q in ps {
                    self.pat(q);
                }
            }
            PatKind::Record(t, fields, _) => {
                self.ty(t);
                super::fit(fields);
                for f in fields {
                    self.ident(&mut f.field);
                    self.pat(&mut f.pattern);
                }
            }
            PatKind::AnonRecord(fields, _) => {
                super::fit(fields);
                for f in fields {
                    self.ident(&mut f.field);
                    self.pat(&mut f.pattern);
                }
            }
            PatKind::Wild
            | PatKind::Bind(_)
            | PatKind::Int(_)
            | PatKind::Str(_)
            | PatKind::Bool(_)
            | PatKind::Const(_)
            | PatKind::Error => {}
        }
    }
}
