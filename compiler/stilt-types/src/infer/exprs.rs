//! Expressions: [`State::infer`] checks each form, here or in the module of its kind.

use stilt_diag::codes;
use stilt_hir::decls::prelude_item;
use stilt_hir::hir::{self, ExprKind, Item, LocalId, Mode, Segment, UnaryOp};
use stilt_syntax::{TextRange, TextSize};

use super::closures::key_path;
use super::types::Sig;
use super::{Cx, Rule, State, error_node, node};
use crate::tast::{self, Callee};
use crate::ty::{Row, Ty, instantiate, is_prelude};

/// Whether an element of a tuple, a list or a call is a spread (variadics.spread-expressions).
pub(super) fn is_spread(e: &hir::Expr) -> bool {
    matches!(e.kind, ExprKind::Spread(_))
}

impl State<'_> {
    /// Infers the type of `e`, checking it against `expected` where there is one. A value of a
    /// polymorphic function type is instantiated afresh unless one is expected
    /// (polymorphism.instantiation).
    pub(super) fn infer(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        e: &hir::Expr,
    ) -> tast::Expr {
        let outer = self.table.enter(e.at);
        let v = self.infer_form(cx, expected, e);
        self.table.leave(outer);
        if expected.is_some_and(|t| self.table.resolve(t).is_poly()) {
            v
        } else {
            self.instantiated(v)
        }
    }

    /// A value parameter, a value of its type (generics.value-parameters-in-body), and a staging
    /// annotation, which means its form, whose place the body records (meta.staging-annotations and
    /// meta.erasure).
    fn meta_expr(&mut self, cx: &mut Cx, expected: Option<&Ty>, e: &hir::Expr) -> tast::Expr {
        match &e.kind {
            ExprKind::ValueParam(g, t) => node(
                tast::ExprKind::ValueParam(g.clone()),
                Ty::from_hir(t, None),
                e.at,
            ),
            ExprKind::Comptime(form) => {
                let keyword = TextRange::new(e.at.start(), form.at.start());
                self.staged.push((keyword, form.at));
                self.infer_form(cx, expected, form)
            }
            _ => unreachable!("only value parameters and staging annotations are meta"),
        }
    }

    /// Infers the type of `e` by its form.
    fn infer_form(&mut self, cx: &mut Cx, expected: Option<&Ty>, e: &hir::Expr) -> tast::Expr {
        let at = e.at;
        match &e.kind {
            ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Str(_)
            | ExprKind::Bool(_)
            | ExprKind::Interpolated(_) => self.literal_expr(cx, e),
            ExprKind::Local(v) => self.local_value(at, *v),
            ExprKind::Func(item) => self.function_value(at, item),
            ExprKind::Const(item) => self.constant_value(at, item),
            ExprKind::Variant(item) => self.variant_value(at, item),
            ExprKind::Member(owner, name) => self.member_value(cx, (at, expected), owner, name),
            ExprKind::KeyRoot => self.key_path_closure(expected, e),
            ExprKind::Field(..) | ExprKind::Call(..) | ExprKind::Index(..) if key_path(e) => {
                self.key_path_closure(expected, e)
            }
            ExprKind::Hole => {
                let ty = expected.cloned().unwrap_or_else(|| self.fresh(at));
                node(tast::ExprKind::Hole, ty, at)
            }
            ExprKind::Tuple(_) | ExprKind::List(_) | ExprKind::Update(..) | ExprKind::Spread(_) => {
                self.aggregate(cx, expected, e)
            }
            ExprKind::Field(base, field) => self.field_access(cx, at, base, field),
            ExprKind::Call(callee, args) => self.call(cx, (at, expected), callee, args),
            ExprKind::Index(base, index) => self.index_expr(cx, at, base, index),
            ExprKind::Struct(t, fields) => self.struct_literal(cx, (at, expected), t, fields),
            ExprKind::Unary(op, operand) => self.unary(cx, expected, at, *op, operand),
            ExprKind::Binary(op, a, b) => self.binary(cx, at, *op, a, b),
            ExprKind::Else(a, b) => self.else_expr(cx, at, a, b),
            ExprKind::Try(operand, arms) => {
                self.try_expr(cx, expected, at, operand, arms.as_deref())
            }
            ExprKind::Raise(value) => self.raise_expr(cx, at, value),
            ExprKind::Return(value) => self.return_expr(cx, at, value.as_deref()),
            ExprKind::Break => node(tast::ExprKind::Break, Ty::never(), at),
            ExprKind::Continue => node(tast::ExprKind::Continue, Ty::never(), at),
            ExprKind::Closure(params, body) => {
                self.unwrapped(|s| s.closure(cx, expected, at, params, body))
            }
            ExprKind::Block(block) => {
                let (b, ty) = self.block_expr(cx, at, expected, block);
                node(tast::ExprKind::Block(b), ty, at)
            }
            ExprKind::If(cond, body, alt) => {
                self.if_expr(cx, expected, at, cond, body, alt.as_deref())
            }
            ExprKind::IfLet(pattern, scrutinee, body, alt) => {
                self.if_let_expr(cx, expected, at, pattern, scrutinee, body, alt.as_deref())
            }
            ExprKind::Match(scrutinee, arms) => self.match_expr(cx, expected, at, scrutinee, arms),
            ExprKind::Loop(body) => self.loop_expr(cx, at, body),
            ExprKind::While(cond, body) => self.while_expr(cx, at, cond, body),
            ExprKind::For(target, iterable, body) => self.for_expr(cx, at, target, iterable, body),
            ExprKind::Error => {
                self.broken = true;
                error_node(at)
            }
            _ => self.handling(cx, expected, e),
        }
    }

    /// An operation named as a value, a handler literal, a `with` or a `resume`
    /// (handlers.handler-literals, handlers.with and handlers.resuming), a `when` (shared.when), a
    /// value parameter or a staging annotation.
    fn handling(&mut self, cx: &mut Cx, expected: Option<&Ty>, e: &hir::Expr) -> tast::Expr {
        let at = e.at;
        match &e.kind {
            ExprKind::Perform(effect, op) => self.operation_value(at, effect, op),
            ExprKind::Handler(h) => self.handler_lit(expected, at, h),
            ExprKind::With(handlers, block) => self.with_expr(cx, expected, at, handlers, block),
            ExprKind::Resume(value) => self.resume_expr(cx, at, value.as_deref()),
            ExprKind::When(held, block) => {
                self.unwrapped(|s| s.when_expr(cx, expected, at, held, block))
            }
            ExprKind::ValueParam(..) | ExprKind::Comptime(_) => self.meta_expr(cx, expected, e),
            ExprKind::Quote(q) => self.quote_expr(cx, at, q),
            _ => unreachable!("`infer_form` gives only the forms of effects and of the meta tier"),
        }
    }

    /// A tuple, a list, an update or a spread, by its form (records.update;
    /// variadics.spread-expressions).
    fn aggregate(&mut self, cx: &mut Cx, expected: Option<&Ty>, e: &hir::Expr) -> tast::Expr {
        let at = e.at;
        match &e.kind {
            // A list literal where an array is expected makes one (generics.array-literals).
            ExprKind::List(es) if expected.and_then(|t| self.array_of(t)).is_some() => {
                let expected = expected.cloned().unwrap_or(Ty::Error);
                let parts = self.array_of(&expected).unwrap_or((Ty::Error, Ty::Error));
                self.array_literal(cx, (at, &expected), parts, es)
            }
            ExprKind::Tuple(es) if es.iter().any(is_spread) => self.spread_tuple(cx, at, es),
            ExprKind::List(es) if es.iter().any(is_spread) => {
                self.spread_list(cx, expected, at, es)
            }
            ExprKind::Tuple(es) => self.tuple_expr(cx, expected, at, es),
            ExprKind::List(es) => self.list_expr(cx, expected, at, es),
            ExprKind::Update(t, base, fields) => {
                self.update_expr(cx, at, (t.as_ref(), base), fields)
            }
            _ => {
                let message = "a spread stands among a tuple's, a list's or a call's elements";
                self.error(codes::E0343, at, message.to_owned());
                error_node(at)
            }
        }
    }

    /// A literal, or a string with interpolated values.
    fn literal_expr(&mut self, cx: &mut Cx, e: &hir::Expr) -> tast::Expr {
        let at = e.at;
        match &e.kind {
            ExprKind::Int(text) => {
                let ty = self.literal(text, false, false, at);
                node(tast::ExprKind::Int(text.clone()), ty, at)
            }
            ExprKind::Float(text) => {
                let ty = self.literal(text, false, true, at);
                node(tast::ExprKind::Float(text.clone()), ty, at)
            }
            ExprKind::Str(s) => node(tast::ExprKind::Str(s.clone()), Ty::str(), at),
            ExprKind::Bool(b) => node(tast::ExprKind::Bool(*b), Ty::bool(), at),
            ExprKind::Interpolated(segments) => {
                let segments = segments.iter().map(|s| self.segment(cx, s)).collect();
                node(tast::ExprKind::Interpolated(segments), Ty::str(), at)
            }
            _ => unreachable!("`infer` checks the other forms"),
        }
    }

    fn raise_expr(&mut self, cx: &mut Cx, at: TextRange, value: &hir::Expr) -> tast::Expr {
        let v = self.infer(cx, None, value);
        // Raised, a value whose type holds a fresh type leaves its region, even where a `try`
        // inside the region would catch it (meta.leaving-arm).
        // E0351 rather than a mismatch with what the row raises elsewhere, as for any value that
        // leaves (`check_leaving`): the row raises the error type then (errors.error-type-raises).
        let left = self.leaving(value.at, &v.ty, 0, "be raised");
        let raised = if left { Ty::Error } else { v.ty.clone() };
        cx.perform(Row::raising(raised), at);
        node(tast::ExprKind::Raise(Box::new(v)), Ty::never(), at)
    }

    fn local_value(&mut self, at: TextRange, v: LocalId) -> tast::Expr {
        let ty = self.locals.get(&v).cloned().unwrap_or(Ty::Error);
        self.uses.insert(at, v);
        node(tast::ExprKind::Local(v), ty, at)
    }

    fn function_value(&mut self, at: TextRange, item: &Item) -> tast::Expr {
        let Some(s) = self.env.decls.function(item) else {
            return error_node(at);
        };
        if s.projection {
            return self.projection_value(at);
        }
        let inst = self.instantiate(at, &Sig::of(s, None), None, at);
        let ty = Ty::func(inst.params, inst.ret, inst.row);
        self.c_use(&Callee::Function(item.clone()), &inst.targs, at);
        node(
            tast::ExprKind::Callee(Callee::Function(item.clone()), inst.targs),
            ty,
            at,
        )
    }

    fn constant_value(&self, at: TextRange, item: &Item) -> tast::Expr {
        match self.env.decls.constant(item) {
            Some(t) => node(
                tast::ExprKind::Constant(item.clone()),
                Ty::from_hir(t, None),
                at,
            ),
            None => error_node(at),
        }
    }

    /// A variant as a value: itself if it has no payload, or else its constructor.
    fn variant_value(&mut self, at: TextRange, item: &Item) -> tast::Expr {
        let Some(v) = self.env.decls.variant(item) else {
            return error_node(at);
        };
        let (ty, args, params) = self.instantiate_type(at, &v.ty);
        let payload: Vec<Ty> = v
            .payload
            .iter()
            .map(|t| instantiate(t, &params, &args))
            .collect();
        if payload.is_empty() {
            return node(
                tast::ExprKind::Construct(item.clone(), args, Vec::new()),
                ty,
                at,
            );
        }
        let fty = Ty::func(
            payload.into_iter().map(|t| (Mode::Let, t)).collect(),
            ty,
            Row::EMPTY,
        );
        node(tast::ExprKind::Constructor(item.clone(), args), fty, at)
    }

    fn unary(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        at: TextRange,
        op: UnaryOp,
        operand: &hir::Expr,
    ) -> tast::Expr {
        // numbers.negative-literals: a `-` directly before a literal is part of it.
        if op == UnaryOp::Neg
            && let ExprKind::Int(text) | ExprKind::Float(text) = &operand.kind
            && operand.at.start() == at.start() + TextSize::from(1)
        {
            let float = matches!(operand.kind, ExprKind::Float(_));
            let ty = self.literal(text, true, float, at);
            let kind = if float {
                tast::ExprKind::Float(text.clone())
            } else {
                tast::ExprKind::Int(text.clone())
            };
            let inner = node(kind, ty.clone(), operand.at);
            return node(tast::ExprKind::Unary(op, Box::new(inner)), ty, at);
        }
        let v = self.infer(cx, expected, operand);
        let rule = match op {
            UnaryOp::Neg => Rule::Negatable,
            UnaryOp::Not => Rule::BoolOrInteger,
        };
        let ty = self.operator(&v.ty, rule, at);
        node(tast::ExprKind::Unary(op, Box::new(v)), ty, at)
    }

    fn segment(&mut self, cx: &mut Cx, s: &Segment) -> tast::Segment {
        match s {
            Segment::Text(t) => tast::Segment::Text(t.clone()),
            Segment::Splice(e, spec) => {
                let v = self.infer(cx, None, e);
                self.obligation(&v.ty, prelude_item("Show"), e.at);
                if let Some(spec) = spec {
                    self.specs.push((v.ty.clone(), spec.clone(), e.at));
                }
                tast::Segment::Splice(Box::new(v), spec.clone())
            }
        }
    }

    fn tuple_expr(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        at: TextRange,
        es: &[hir::Expr],
    ) -> tast::Expr {
        // An element checked against a type has that type, so a `Never` element converts
        // (declarations.never).
        // A spread among the expected elements gives them no expected types until its pack
        // is known (variadics.pack-inference).
        let expected_items: Vec<Option<Ty>> = match expected.map(|t| self.resolved(t)) {
            Some(Ty::Tuple(ts))
                if self.table.elements(&ts).len() == es.len()
                    && self
                        .table
                        .elements(&ts)
                        .iter()
                        .all(|t| t.as_spread().is_none()) =>
            {
                self.table.elements(&ts).into_iter().map(Some).collect()
            }
            Some(Ty::Error) => es.iter().map(|_| Some(Ty::Error)).collect(),
            _ => es.iter().map(|_| None).collect(),
        };
        let items: Vec<tast::Expr> = es
            .iter()
            .zip(&expected_items)
            .map(|(e, x)| self.infer_checked(cx, x.as_ref(), e))
            .collect();
        let types = items
            .iter()
            .zip(expected_items)
            .map(|(i, x)| x.unwrap_or_else(|| i.ty.clone()))
            .collect();
        node(tast::ExprKind::Tuple(items), Ty::Tuple(types), at)
    }

    fn list_expr(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        at: TextRange,
        es: &[hir::Expr],
    ) -> tast::Expr {
        // Without an expected element type, the first element establishes one, with room for
        // the rows of the later ones.
        let (items, elem) = match (expected.map(|t| self.resolved(t)), es) {
            (Some(Ty::Con(item, args)), _) if is_prelude(&item, "List") && args.len() == 1 => {
                let t = &args[0];
                (es.iter().map(|e| self.check(cx, t, e)).collect(), t.clone())
            }
            (Some(Ty::Error), _) => (
                es.iter().map(|e| self.check(cx, &Ty::Error, e)).collect(),
                Ty::Error,
            ),
            (_, []) => (Vec::new(), self.fresh(at)),
            (_, [first, rest @ ..]) => {
                let v = self.infer(cx, None, first);
                let elem = self.widen(&v.ty);
                self.subsume(first.at, &elem, &v.ty);
                let mut items = vec![v];
                items.extend(rest.iter().map(|e| self.check(cx, &elem, e)));
                (items, elem)
            }
        };
        node(tast::ExprKind::List(items), Ty::list(elem), at)
    }

    fn index_expr(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        base: &hir::Expr,
        index: &hir::Expr,
    ) -> tast::Expr {
        let b = self.infer(cx, None, base);
        let index_node = |b, i, t| node(tast::ExprKind::Index(Box::new(b), Box::new(i)), t, at);
        match self.known(base.at, &b.ty) {
            None => {
                self.abandon(cx, index);
                error_node(at)
            }
            Some(Ty::Con(item, args)) if is_prelude(&item, "List") && args.len() == 1 => {
                let i = self.check(cx, &Ty::i64(), index);
                index_node(b, i, args[0].clone())
            }
            // generics.array-elements: an array is indexed by an `i64`, as a list is.
            Some(t) if t.arrayed().is_some() => {
                let elem = t.arrayed().map_or(Ty::Error, |(elem, _)| elem.clone());
                let i = self.check(cx, &Ty::i64(), index);
                index_node(b, i, elem)
            }
            // views.functions-of-views: a view of a list is indexed as the list is.
            Some(t) if self.view_elements(&t).is_some() => {
                let elem = self.view_elements(&t).unwrap_or(Ty::Error);
                let i = self.check(cx, &Ty::i64(), index);
                index_node(b, i, elem)
            }
            Some(Ty::Con(item, args)) if is_prelude(&item, "Map") && args.len() == 2 => {
                // std.map-key-bounds: indexing finds a key, as the map's methods do.
                self.obligation(&args[0], prelude_item("Eq"), at);
                self.obligation(&args[0], prelude_item("Hash"), at);
                let i = self.check(cx, &args[0], index);
                index_node(b, i, args[1].clone())
            }
            // variadics.pack-tuples: a pack tuple's arity isn't known, so no index reads it.
            Some(t) if self.pack_tuple(&t) => {
                self.abandon(cx, index);
                self.unknown_arity(at, "no index reads it");
                error_node(at)
            }
            // shared.std-sync and shared.when: a `Shared<T>` is indexed only inside a `when`.
            Some(t) if t.shared().is_some() => {
                self.abandon(cx, index);
                let message = format!(
                    "a value of type `{}` can't be indexed: its value is reached only inside a \
                     `when` that names it",
                    self.show(&t)
                );
                self.error(codes::E0317, at, message);
                error_node(at)
            }
            Some(t) => {
                self.abandon(cx, index);
                let message = format!("a value of type `{}` can't be indexed", self.show(&t));
                self.error(codes::E0317, at, message);
                error_node(at)
            }
        }
    }

    fn else_expr(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        a: &hir::Expr,
        b: &hir::Expr,
    ) -> tast::Expr {
        let x = self.infer(cx, None, a);
        self.option_fallback(cx, at, a, x, b)
    }

    /// expressions.option-fallback: the `Option` fallback `a else b` at `at`, once `a` is inferred
    /// as `x`.
    pub(super) fn option_fallback(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        a: &hir::Expr,
        x: tast::Expr,
        b: &hir::Expr,
    ) -> tast::Expr {
        let inner = if *self.table.resolve(&x.ty) == Ty::Error {
            Ty::Error
        } else {
            let inner = self.fresh(a.at);
            if self.fits(a.at, &Ty::option(inner.clone()), &x.ty) {
                inner
            } else {
                Ty::Error
            }
        };
        let y = self.check(cx, &inner, b);
        node(tast::ExprKind::Else(Box::new(x), Box::new(y)), inner, at)
    }

    fn return_expr(&mut self, cx: &mut Cx, at: TextRange, value: Option<&hir::Expr>) -> tast::Expr {
        let ret = cx.ret.clone();
        let v = if let Some(value) = value {
            let leaves = (&ret, cx.returns_at, "be returned from it");
            Some(Box::new(self.check_leaving(cx, leaves, value)))
        } else {
            self.expect(at, &ret, &Ty::unit());
            None
        };
        node(tast::ExprKind::Return(v), Ty::never(), at)
    }
}
