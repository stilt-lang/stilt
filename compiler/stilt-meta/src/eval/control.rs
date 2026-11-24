//! Blocks, statements and control (expressions.loops, expressions.if and expressions.match;
//! effects.catch): a block's value is its last expression's, a loop turns until it breaks, each
//! turn a step of the run (macros.step-limits), and a raised error leaves each expression
//! until a `catch` takes it.

use std::sync::Arc;

use stilt_types::tast::{Arm, Binding, Block, Catch, Expr, ExprKind, Iterable, StmtKind};

use super::calls::closure;
use super::{Flow, Frame, Machine, R, panic};
use crate::value::Value;

impl<'a> Machine<'a> {
    /// The forms of control, and the others that the run doesn't evaluate.
    pub(super) fn control(&mut self, fr: &mut Frame<'a>, e: &'a Expr) -> R<'a> {
        match &e.kind {
            ExprKind::Block(b) => self.block(fr, b),
            ExprKind::If(cond, then, alt) => {
                if self.expr(fr, cond)?.as_bool() {
                    self.block(fr, then)
                } else {
                    alt.as_ref()
                        .map_or_else(|| Ok(Value::unit()), |a| self.expr(fr, a))
                }
            }
            ExprKind::IfLet(p, scrutinee, then, alt) => {
                let v = self.expr(fr, scrutinee)?;
                if self.bind_pattern(fr, p, v)? {
                    self.block(fr, then)
                } else {
                    alt.as_ref()
                        .map_or_else(|| Ok(Value::unit()), |a| self.expr(fr, a))
                }
            }
            ExprKind::Match(scrutinee, arms) => {
                let v = self.expr(fr, scrutinee)?;
                self.arms(fr, arms, &v)?
                    .map_or_else(|| panic("unreachable", "no arm matched"), Ok)
            }
            ExprKind::Loop(b) => self.repeat(fr, b, None),
            ExprKind::While(cond, b) => self.repeat(fr, b, Some(cond)),
            ExprKind::For(p, iterable, b) => self.for_(fr, p, iterable, b),
            ExprKind::Else(a, b) => self.else_(fr, a, b),
            ExprKind::Try(e, catch) => self.try_(fr, e, catch.as_ref()),
            ExprKind::Raise(e) => Err(Flow::Raise(self.expr(fr, e)?)),
            ExprKind::Return(e) => {
                let v = match e {
                    Some(e) => self.expr(fr, e)?,
                    None => Value::unit(),
                };
                Err(Flow::Return(v))
            }
            ExprKind::Break => Err(Flow::Break),
            ExprKind::Continue => Err(Flow::Continue),
            ExprKind::Closure(params, body) => Ok(closure(fr, params, body, &e.ty)),
            ExprKind::Constant(item) => self.constant(item, None),
            ExprKind::MemberConstant(owner, name, _) => self.constant(owner, Some(*name)),
            ExprKind::Quote(q) => self.quote(fr, q),
            ExprKind::Hole => panic("hole", "reached a hole"),
            _ => self.advanced(fr, e),
        }
    }

    /// The forms of the advanced tier and the meta tier: effects (handlers.with), `when`
    /// (shared.when), projections (projections.declaring-projection), reflection (meta.reflects)
    /// and value parameters (generics.value-parameters).
    fn advanced(&mut self, fr: &mut Frame<'a>, e: &'a Expr) -> R<'a> {
        match &e.kind {
            ExprKind::Handler(h) => self.handler_literal(fr, h),
            ExprKind::With(h, _, _, b) => self.with(fr, h, b),
            ExprKind::Resume(v) => {
                let v = match v {
                    Some(v) => self.expr(fr, v)?,
                    None => Value::unit(),
                };
                self.resume(v)
            }
            ExprKind::When(names, b) => self.when(fr, names, b),
            ExprKind::Project(..) => self.project_read(fr, e),
            ExprKind::Spread(_) => unreachable!(
                "a spread stands among elements or arguments, which evaluate it (variadics.spread-expressions)"
            ),
            ExprKind::Reflect(what, ty) => Ok(self.reflect(fr, *what, ty)),
            ExprKind::Bound(ty, traits) => Ok(Value::Bool(self.bound_holds(fr, ty, traits))),
            ExprKind::ValueParam(g) => Ok(super::reflect::value_param(fr, g, &e.ty)),
            _ => panic(
                "check-error",
                "this code has an error, which `check` reports",
            ),
        }
    }

    /// The value of a constant, or of a type's constant `member`, computed once in the run.
    fn constant(
        &mut self,
        owner: &'a stilt_hir::hir::Item,
        member: Option<stilt_hir::hir::Name>,
    ) -> R<'a> {
        use crate::image::FnCode;
        use stilt_mir::FnRef;
        use stilt_types::tast::{Code, Definition};
        let key = (owner.clone(), member);
        if let Some(v) = self.constants.get(&key) {
            return Ok(v.clone());
        }
        let f = match member {
            Some(name) => FnRef::MemberConst(owner.clone(), name),
            None => FnRef::Const(owner.clone()),
        };
        let image = self.image;
        let info = match image.function(&f).map(|(code, _)| code) {
            Some(FnCode::Body { info, .. }) => Arc::clone(info),
            Some(FnCode::Native(_)) => {
                let v = crate::natives::constant(owner, member.as_deref().unwrap_or(""));
                self.constants.insert(key, v.clone());
                return Ok(v);
            }
            Some(FnCode::Broken) => {
                return panic(
                    "check-error",
                    "this code has an error, which `check` reports",
                );
            }
            None => unreachable!("the image holds every constant a run reaches"),
        };
        let body = info.body;
        let mut frame = Frame::new(info);
        let v = match &body.code {
            Definition::Code(Code::Expr(e)) => self.expr(&mut frame, e)?,
            Definition::Code(Code::Block(b)) => self.block(&mut frame, b)?,
            Definition::Native => crate::natives::constant(owner, member.as_deref().unwrap_or("")),
            Definition::Broken => {
                return panic(
                    "check-error",
                    "this code has an error, which `check` reports",
                );
            }
        };
        self.constants.insert(key, v.clone());
        Ok(v)
    }

    /// A block's statements, its value its last expression's.
    pub(crate) fn block(&mut self, fr: &mut Frame<'a>, b: &'a Block) -> R<'a> {
        let mut last = None;
        for s in b {
            last = None;
            match &s.kind {
                StmtKind::Let(binding) | StmtKind::Var(binding) => self.binding(fr, binding)?,
                StmtKind::Assign(op, place, value) => self.assign(fr, *op, place, value)?,
                StmtKind::Assert(e) => {
                    if !self.expr(fr, e)?.as_bool() {
                        return panic("assert", "the assertion is false");
                    }
                }
                StmtKind::Yield(place) => self.yield_place(fr, place)?,
                StmtKind::Expr(e) => last = Some(self.expr(fr, e)?),
            }
        }
        Ok(last.unwrap_or_else(Value::unit))
    }

    /// `let p = e` and `var p = e`, with `else` when `p` can fail to match.
    fn binding(&mut self, fr: &mut Frame<'a>, b: &'a Binding) -> Result<(), Flow<'a>> {
        let v = self.expr(fr, &b.value)?;
        if self.bind_pattern(fr, &b.pattern, v)? {
            return Ok(());
        }
        match &b.otherwise {
            Some(e) => self.expr(fr, e).map(|_| ()),
            None => panic("unreachable", "a binding's pattern didn't match"),
        }
    }

    /// The body of the first arm that matches `v`, if one does.
    pub(super) fn arms(
        &mut self,
        fr: &mut Frame<'a>,
        arms: &'a [Arm],
        v: &Value<'a>,
    ) -> Result<Option<Value<'a>>, Flow<'a>> {
        for arm in arms {
            if !self.bind_pattern(fr, &arm.pattern, v.clone())? {
                continue;
            }
            if let Some(g) = &arm.guard
                && !self.expr(fr, g)?.as_bool()
            {
                continue;
            }
            return self.expr(fr, &arm.body).map(Some);
        }
        Ok(None)
    }

    /// `loop`, or `while cond`, whose condition is outside its body.
    fn repeat(&mut self, fr: &mut Frame<'a>, b: &'a Block, cond: Option<&'a Expr>) -> R<'a> {
        loop {
            if let Some(c) = cond
                && !self.expr(fr, c)?.as_bool()
            {
                return Ok(Value::unit());
            }
            if !self.turn(fr, b)? {
                return Ok(Value::unit());
            }
        }
    }

    /// One turn of a loop's body, and whether the loop goes on.
    fn turn(&mut self, fr: &mut Frame<'a>, b: &'a Block) -> Result<bool, Flow<'a>> {
        self.run.step()?;
        match self.block(fr, b) {
            Ok(_) | Err(Flow::Continue) => Ok(true),
            Err(Flow::Break) => Ok(false),
            Err(other) => Err(other),
        }
    }

    /// `for p in it`: a list's elements, a map's entries, an iterator's elements as it gives
    /// them (views.for-over-view), a range's numbers, or the fields or the cases of a type, each
    /// with its fresh type (meta.fields and meta.variant-cases).
    fn for_(
        &mut self,
        fr: &mut Frame<'a>,
        pat: &'a stilt_types::tast::Pat,
        it: &'a Iterable,
        body: &'a Block,
    ) -> R<'a> {
        let source = match it {
            Iterable::Range(from, to, inclusive) => {
                let start = self.expr(fr, from)?.as_int();
                let end = self.expr(fr, to)?;
                let Value::Int(stop, k) = end else {
                    unreachable!("a range's bounds are integers, as checking found")
                };
                let stop = if *inclusive { stop } else { stop - 1 };
                let items = (start..=stop).map(move |x| Value::Int(x, k));
                return self.each(fr, pat, body, items);
            }
            Iterable::Iter(source) => source,
        };
        if let Some(elements) = self.reflected_elements(fr, &source.ty) {
            return self.each_reflected(fr, pat, body, elements);
        }
        let v = self.expr(fr, source)?;
        match self.thaw(v)? {
            Value::List(xs) => self.each(fr, pat, body, xs.get().clone().into_iter()),
            Value::Map(map) => {
                let entries = map.entries.get().clone().into_iter();
                let pairs = entries.map(|(k, v)| Value::tuple(vec![k, v]));
                self.each(fr, pat, body, pairs)
            }
            Value::Iter(it) => {
                let mut cursor = crate::natives::Cursor::new(&it);
                while let Some(x) = cursor.next(self)? {
                    self.bind_pattern(fr, pat, x)?;
                    if !self.turn(fr, body)? {
                        break;
                    }
                }
                Ok(Value::unit())
            }
            _ => unreachable!("a `for` goes through a list, a map, a view or an iterator"),
        }
    }

    /// Runs a loop's body on each of `items` in turn, until it breaks.
    fn each(
        &mut self,
        fr: &mut Frame<'a>,
        pat: &'a stilt_types::tast::Pat,
        body: &'a Block,
        items: impl Iterator<Item = Value<'a>>,
    ) -> R<'a> {
        for v in items {
            self.bind_pattern(fr, pat, v)?;
            if !self.turn(fr, body)? {
                break;
            }
        }
        Ok(Value::unit())
    }

    /// Runs a loop's body on each field or case of a type, its pattern's fresh type bound to
    /// the field's or the payload's type.
    fn each_reflected(
        &mut self,
        fr: &mut Frame<'a>,
        pat: &'a stilt_types::tast::Pat,
        body: &'a Block,
        elements: Vec<stilt_types::ty::Ty>,
    ) -> R<'a> {
        for (i, element) in elements.into_iter().enumerate() {
            super::reflect::bind_fresh(fr, &pat.ty, &element);
            self.bind_pattern(fr, pat, Value::i64(i128::try_from(i).unwrap_or(0)))?;
            if !self.turn(fr, body)? {
                break;
            }
        }
        Ok(Value::unit())
    }

    /// `a else b`: an `Option`'s payload, a `Result`'s value, or `b`.
    fn else_(&mut self, fr: &mut Frame<'a>, a: &'a Expr, b: &'a Expr) -> R<'a> {
        let v = self.expr(fr, a)?;
        if let Value::Variant(var) = &v
            && matches!(&*var.0.name, "Some" | "Ok")
            && let Some(x) = var.1.first()
        {
            return Ok(x.clone());
        }
        self.expr(fr, b)
    }

    /// `try e`, and `try e catch { … }`, whose arms take the error `e` raises.
    fn try_(&mut self, fr: &mut Frame<'a>, e: &'a Expr, catch: Option<&'a Catch>) -> R<'a> {
        match (self.expr(fr, e), catch) {
            (Err(Flow::Raise(err)), Some(c)) => match self.arms(fr, &c.arms, &err)? {
                Some(v) => Ok(v),
                None => Err(Flow::Raise(err)),
            },
            (result, _) => result,
        }
    }
}
