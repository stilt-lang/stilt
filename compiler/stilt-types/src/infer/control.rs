//! Branches and loops: `if`, `if let`, `match`, `try … catch`, `loop`, `while` and `for`.

use stilt_diag::{Edit, Fix, codes};
use stilt_hir::hir::{self, ExprKind, Iterable, PatKind, Segment, StmtKind};
use stilt_syntax::TextRange;

use super::effects::Reported;
use super::refutable::Named;
use super::{Cx, Rule, State, UnitSite, node};
use crate::tast;
use crate::ty::{Kind, Ty};

/// Whether a loop's body holds a `break` that exits it, outside any nested loop or closure
/// (expressions.break-and-continue).
fn breaks(e: &hir::Expr) -> bool {
    match &e.kind {
        ExprKind::Break => true,
        // The head of a `while` and the iterable of a `for` are outside its body.
        ExprKind::While(cond, _) => breaks(cond),
        ExprKind::For(_, iterable, _) => match &**iterable {
            Iterable::Iter(source) => breaks(source),
            Iterable::Range(a, b, _) => breaks(a) || breaks(b),
        },
        ExprKind::Block(b) | ExprKind::When(_, b) => breaks_block(b),
        ExprKind::If(c, b, alt) | ExprKind::IfLet(_, c, b, alt) => {
            breaks(c) || breaks_block(b) || alt.as_deref().is_some_and(breaks)
        }
        ExprKind::Match(s, arms) => breaks(s) || arms.iter().any(breaks_arm),
        ExprKind::Try(e, arms) => breaks(e) || arms.iter().flatten().any(breaks_arm),
        ExprKind::Field(e, _)
        | ExprKind::Unary(_, e)
        | ExprKind::Raise(e)
        | ExprKind::Comptime(e)
        | ExprKind::Spread(e) => breaks(e),
        ExprKind::Update(_, base, fields) => {
            breaks(base) || fields.iter().any(|f| breaks(&f.value))
        }
        ExprKind::Return(e) | ExprKind::Resume(e) => e.as_deref().is_some_and(breaks),
        ExprKind::With(handlers, b) => handlers.iter().any(breaks) || breaks_block(b),
        ExprKind::Call(f, args) => breaks(f) || args.iter().any(|a| breaks(&a.value)),
        ExprKind::Index(a, b) | ExprKind::Binary(_, a, b) | ExprKind::Else(a, b) => {
            breaks(a) || breaks(b)
        }
        ExprKind::Tuple(es) | ExprKind::List(es) => es.iter().any(breaks),
        ExprKind::Quote(q) => q.splices.iter().any(|s| breaks(&s.value)),
        ExprKind::Struct(_, fields) => fields.iter().any(|f| breaks(&f.value)),
        ExprKind::Interpolated(segments) => segments.iter().any(|s| match s {
            Segment::Splice(e, _) => breaks(e),
            Segment::Text(_) => false,
        }),
        // A `break` in a nested loop or closure exits that.
        ExprKind::Loop(_)
        | ExprKind::Closure(..)
        | ExprKind::Handler(_)
        | ExprKind::Perform(..)
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Local(_)
        | ExprKind::Func(_)
        | ExprKind::Const(_)
        | ExprKind::Variant(_)
        | ExprKind::Member(..)
        | ExprKind::KeyRoot
        | ExprKind::Hole
        | ExprKind::Continue
        | ExprKind::ValueParam(..)
        | ExprKind::Bound(_)
        | ExprKind::Error => false,
    }
}

fn breaks_arm(a: &hir::Arm) -> bool {
    a.guard.as_deref().is_some_and(breaks) || breaks(&a.body)
}

fn breaks_block(b: &[hir::Stmt]) -> bool {
    b.iter().any(|s| match &s.kind {
        StmtKind::Let(b) | StmtKind::Var(b) => breaks(&b.value),
        StmtKind::Assign(_, p, v) => breaks(p) || breaks(v),
        StmtKind::Assert(e) | StmtKind::Yield(e) | StmtKind::Expr(e) => breaks(e),
    })
}

impl State<'_> {
    /// Whether an arm's pattern is a catch-all, which may give a reason
    /// (effects.catch-alls-need-reason): `_`, a binding, or a name with an error, written with a
    /// module or without one (patterns.pattern-forms).
    fn catch_all(&self, p: &hir::Pat) -> bool {
        match &p.kind {
            PatKind::Wild | PatKind::Bind(_) | PatKind::Error => true,
            PatKind::Bare(..) => matches!(self.bare.get(&p.at), Some(Named::Error)),
            _ => false,
        }
    }

    /// An arm of a `match` or a `catch`. Only a `catch` arm can give a reason, and the grammar
    /// gives it no guard then.
    fn arm(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        scrutinee: &Ty,
        a: &hir::Arm,
    ) -> tast::Arm {
        self.forget_fresh();
        let pattern = self.pattern(cx, &a.pattern, scrutinee);
        // meta.fresh-types: the fresh types of a shape's case are the arm's.
        let region = self.open_region("arm");
        let guard = a
            .guard
            .as_ref()
            .map(|g| Box::new(self.check(cx, &Ty::bool(), g)));
        // effects.catch-alls-need-reason
        if let Some((_, at)) = &a.because
            && !self.catch_all(&a.pattern)
        {
            let message = "only a catch-all arm gives a reason with `because`";
            let reason = TextRange::new(a.pattern.at.end(), at.end());
            let fix = Fix::new("delete the reason", vec![Edit::delete(reason)]);
            self.error_fixed(codes::E0504, *at, message.to_owned(), vec![fix]);
        }
        let body = self.infer_checked(cx, expected, &a.body);
        if region {
            self.arm_value(&body, expected);
        }
        self.close_region(region);
        tast::Arm {
            pattern,
            guard,
            because: a.because.is_some(),
            body,
        }
    }

    /// The arms of a `match` or a `catch`, each checked against the expected type, or else
    /// against the type the first that isn't `Never` gives the rest, starting from `common`.
    fn arms(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        scrutinee: &Ty,
        arms: &[hir::Arm],
        mut common: Option<Ty>,
    ) -> (Vec<tast::Arm>, Ty) {
        let mut checked = Vec::new();
        for a in arms {
            if expected.is_some() || common.is_some() {
                let against = expected.cloned().or_else(|| common.clone());
                checked.push(self.arm(cx, against.as_ref(), scrutinee, a));
            } else {
                let a = self.arm(cx, None, scrutinee, a);
                common = self.settled(&a.body.ty, a.body.at);
                checked.push(a);
            }
        }
        let ty = expected.cloned().or(common).unwrap_or_else(Ty::never);
        (checked, ty)
    }

    pub(super) fn if_expr(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        at: TextRange,
        cond: &hir::Expr,
        body: &[hir::Stmt],
        alt: Option<&hir::Expr>,
    ) -> tast::Expr {
        if let ExprKind::Bound(test) = &cond.kind {
            return self.bound_if(cx, (expected, at), cond, test, (body, alt));
        }
        let c = Box::new(self.check(cx, &Ty::bool(), cond));
        let (b, alt, ty) = self.branches(cx, expected, at, body, alt);
        node(tast::ExprKind::If(c, b, alt), ty, at)
    }

    /// An `if let`, whose expression is matched as a `match` arm would be, and which is typed
    /// as an `if` (expressions.if-let; patterns.match).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn if_let_expr(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        at: TextRange,
        pattern: &hir::Pat,
        scrutinee: &hir::Expr,
        body: &[hir::Stmt],
        alt: Option<&hir::Expr>,
    ) -> tast::Expr {
        let s = self.infer(cx, None, scrutinee);
        self.forget_fresh();
        let p = self.pattern(cx, pattern, &s.ty.clone());
        let region = self.open_region("branch");
        let (b, ty) = self.block_expr(cx, at, expected.filter(|_| alt.is_some()), body);
        if region {
            let value = node(tast::ExprKind::Block(b.clone()), ty.clone(), at);
            self.arm_value(&value, expected.filter(|_| alt.is_some()));
        }
        self.close_region(region);
        let (alt, ty) = self.after_branch(cx, (expected, at), ty, alt);
        node(tast::ExprKind::IfLet(p, Box::new(s), b, alt), ty, at)
    }

    /// The branches of an `if` or an `if let`, and its type (expressions.if).
    pub(super) fn branches(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        at: TextRange,
        body: &[hir::Stmt],
        alt: Option<&hir::Expr>,
    ) -> (tast::Block, Option<Box<tast::Expr>>, Ty) {
        let (b, ty) = self.block_expr(cx, at, expected.filter(|_| alt.is_some()), body);
        let (alt, ty) = self.after_branch(cx, (expected, at), ty, alt);
        (b, alt, ty)
    }

    /// What follows the first branch of an `if`, whose block has type `ty`: its `else`, checked
    /// against the type that branch gives, and the `if`'s type.
    pub(super) fn after_branch(
        &mut self,
        cx: &mut Cx,
        (expected, at): (Option<&Ty>, TextRange),
        ty: Ty,
        alt: Option<&hir::Expr>,
    ) -> (Option<Box<tast::Expr>>, Ty) {
        let Some(alt) = alt else {
            // A block whose type is still unknown decides the `if`'s at the end of the body,
            // and a block with a value has an error there, so the `if` reports one error or
            // the other.
            let if_ty = match (self.resolved(&ty), self.table.unsolved(&ty).map(|v| v.kind)) {
                (Ty::Var(_), Some(Kind::Any)) => self.fresh(at),
                (Ty::Tuple(ts), _) if ts.is_empty() => Ty::unit(),
                (Ty::Error, _) => Ty::unit(),
                (t, _) if t == Ty::never() => Ty::unit(),
                _ => Ty::Error,
            };
            self.units
                .push((ty, UnitSite::IfWithoutElse(if_ty.clone()), at));
            return (None, if_ty);
        };
        let common = self.settled(&ty, at);
        let (a, ty) = match (expected, common) {
            (Some(t), _) => (self.check(cx, t, alt), t.clone()),
            (None, Some(common)) => (self.check(cx, &common, alt), common),
            (None, None) => {
                let a = self.infer(cx, None, alt);
                let ty = a.ty.clone();
                (a, ty)
            }
        };
        (Some(Box::new(a)), ty)
    }

    pub(super) fn match_expr(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        at: TextRange,
        scrutinee: &hir::Expr,
        arms: &[hir::Arm],
    ) -> tast::Expr {
        let s = self.infer(cx, None, scrutinee);
        let (checked, ty) = self.arms(cx, expected, &s.ty.clone(), arms, None);
        node(tast::ExprKind::Match(Box::new(s), checked), ty, at)
    }

    pub(super) fn try_expr(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        at: TextRange,
        operand: &hir::Expr,
        arms: Option<&[hir::Arm]>,
    ) -> tast::Expr {
        let mut inner = Cx::new(cx.ret.clone());
        inner.returns_at = cx.returns_at;
        inner.yields.clone_from(&cx.yields);
        inner.known.clone_from(&cx.known);
        inner.resume.clone_from(&cx.resume);
        let calls = self.unmarked.len();
        let (x, fitted) = match expected {
            Some(t) => self.check_fits(&mut inner, t, operand),
            None => (self.infer(&mut inner, None, operand), true),
        };
        // The `try` marks every call in its operand (effects.marking).
        self.unmarked.truncate(calls);
        let Some(arms) = arms else {
            cx.effects.extend(inner.effects);
            // An operand that doesn't fit the expected type has been reported, so the `try`
            // has the error type rather than reporting it again.
            let ty = if fitted { x.ty.clone() } else { Ty::Error };
            return node(tast::ExprKind::Try(Box::new(x), None), ty, at);
        };
        // effects.catch: the arms handle the operand's raise, and every other effect of the
        // operand passes through, including those its open rows gain later. The error type is
        // the first raise's, the error type where the operand holds an expression of the error
        // type, which may raise it (errors.error-type-raises), or a variable while an open row may
        // still raise.
        let raised = inner
            .effects
            .iter()
            .find_map(|(row, _)| self.table.row_contents(row).raise.map(|t| *t));
        let error_ty = match raised {
            Some(t) => t,
            None if tast::walk::exists(&x, &|e| e.ty == Ty::Error) => Ty::Error,
            None if inner.effects.iter().any(|(row, _)| self.table.is_open(row)) => {
                let v = self.fresh(at);
                self.catch_errors.push(v.clone());
                v
            }
            None => Ty::never(),
        };
        let passed = self.table.fresh_row(false);
        let mut reported = Reported::default();
        for (row, row_at) in &inner.effects {
            let handled = crate::ty::Handled::Raise(error_ty.clone());
            let problems = self.table.fit(&handled, row, &passed);
            self.report(&mut reported, (*row_at, false), problems);
        }
        cx.perform(passed, at);
        let common = if expected.is_none() {
            self.settled(&x.ty, operand.at)
        } else {
            None
        };
        let (checked, ty) = self.arms(cx, expected, &error_ty, arms, common);
        let catch = tast::Catch {
            error: error_ty,
            arms: checked,
        };
        node(tast::ExprKind::Try(Box::new(x), Some(catch)), ty, at)
    }

    pub(super) fn loop_expr(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        body: &[hir::Stmt],
    ) -> tast::Expr {
        let b = self.loop_body(cx, at, body);
        let ty = if breaks_block(body) {
            Ty::unit()
        } else {
            Ty::never()
        };
        node(tast::ExprKind::Loop(b), ty, at)
    }

    pub(super) fn while_expr(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        cond: &hir::Expr,
        body: &[hir::Stmt],
    ) -> tast::Expr {
        let c = self.check(cx, &Ty::bool(), cond);
        let b = self.loop_body(cx, at, body);
        node(tast::ExprKind::While(Box::new(c), b), Ty::unit(), at)
    }

    /// The elements of a view of a list (views.functions-of-views and views.for-over-view).
    pub(super) fn view_elements(&self, t: &Ty) -> Option<Ty> {
        self.resolved(t.viewed()?).listed().cloned()
    }

    pub(super) fn for_expr(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        target: &hir::Pat,
        iterable: &Iterable,
        body: &[hir::Stmt],
    ) -> tast::Expr {
        self.forget_fresh();
        let (it, elem) = match iterable {
            Iterable::Iter(source) => {
                let s = self.infer(cx, None, source);
                let elem = match self.known(source.at, &s.ty) {
                    Some(t) if self.pack_tuple(&t) => {
                        self.unknown_arity(source.at, "a loop can't go through it");
                        Ty::Error
                    }
                    Some(Ty::Con(item, args))
                        if crate::ty::is_prelude(&item, "List") && args.len() == 1 =>
                    {
                        args[0].clone()
                    }
                    Some(Ty::Con(item, args))
                        if crate::ty::is_prelude(&item, "Map") && args.len() == 2 =>
                    {
                        Ty::Tuple(args)
                    }
                    // generics.array-iteration: an array yields its elements.
                    Some(t) if t.arrayed().is_some() => {
                        t.arrayed().map_or(Ty::Error, |(elem, _)| elem.clone())
                    }
                    // views.for-over-view: a view of a list, and an iterator, yield their elements.
                    Some(t) if self.view_elements(&t).is_some() => {
                        self.view_elements(&t).unwrap_or(Ty::Error)
                    }
                    Some(t) if t.iterated().is_some() => t.iterated().cloned().unwrap_or(Ty::Error),
                    // meta.fields and meta.variant-cases: fields and cases, whose types are fresh
                    // in the loop's body.
                    Some(t) if let Some(elem) = self.reflected_element(&t) => elem,
                    Some(t) => {
                        let message = format!(
                            "expected a list, a map or a range, found `{}`",
                            self.show(&t)
                        );
                        self.error(codes::E0311, source.at, message);
                        Ty::Error
                    }
                    None => Ty::Error,
                };
                (tast::Iterable::Iter(Box::new(s)), elem)
            }
            Iterable::Range(a, b, inclusive) => {
                let x = self.infer(cx, None, a);
                let y = self.check(cx, &x.ty, b);
                let elem = self.operator(&x.ty, Rule::Integer, a.at);
                (
                    tast::Iterable::Range(Box::new(x), Box::new(y), *inclusive),
                    elem,
                )
            }
        };
        let p = self.pattern(cx, target, &elem);
        self.require_irrefutable(target);
        let region = self.open_region("loop's body");
        let b = self.loop_body(cx, at, body);
        self.close_region(region);
        node(tast::ExprKind::For(p, Box::new(it), b), Ty::unit(), at)
    }
}
