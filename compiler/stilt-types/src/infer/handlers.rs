//! Effects and handlers: performances, handler literals and `resume`. Rule numbers in
//! comments refer to the Reference's handlers chapter.

use stilt_diag::codes;
use stilt_hir::decls::{EffectInfo, OperationSig};
use stilt_hir::hir::{self, Arg, HandlerLit, HandlerOp, Ident, Item, Mode};
use stilt_syntax::TextRange;

use super::{Cx, State, error_node, node};
use crate::tast::{self, Callee};
use crate::ty::{Handled, HandlerTy, Row, Subst, Ty};

/// An operation's parameters, result and row, for the effect's arguments.
type OpSig = (Vec<(Mode, Ty)>, Ty, Row);

impl State<'_> {
    /// handlers.performing-operation: the type arguments of `effect` where it is performed: those
    /// of the row that the code must fit, as an enclosing `with` or the signature gives them, or
    /// new variables, which the first performance fixes.
    fn effect_args(&mut self, cx: &Cx, at: TextRange, effect: &Item, info: &EffectInfo) -> Vec<Ty> {
        match cx.known.iter().find(|(e, _)| e == effect) {
            Some((_, args)) if args.len() == info.params.len() => args.clone(),
            _ => info.params.iter().map(|_| self.fresh(at)).collect(),
        }
    }

    /// handlers.with: the effects that the rows of the operations of a handler of `hty` hold, each
    /// once, which its bodies perform on the handlers outside the `with` that installs it. A
    /// raise or `io` of those rows is the performance's, whose row holds it
    /// (handlers.performing-operation).
    pub(super) fn operation_effects(&self, hty: &HandlerTy) -> Row {
        let mut row = Row::EMPTY;
        let Some(info) = self.env.decls.effect_info(&hty.effect) else {
            return row;
        };
        if info.params.len() != hty.args.len() {
            return row;
        }
        for o in &info.ops {
            let (_, _, r) = self.operation_sig(info, &hty.args, o);
            for (e, args) in r.effects {
                if row.effect(&e).is_none() {
                    row.effects.push((e, args));
                }
            }
        }
        row
    }

    /// An operation's parameters, result and row, for the effect's arguments `args`.
    fn operation_sig(&self, info: &EffectInfo, args: &[Ty], o: &OperationSig) -> OpSig {
        let sub = Subst {
            self_ty: None,
            types: info
                .params
                .iter()
                .cloned()
                .zip(args.iter().cloned())
                .collect(),
            rows: Vec::new(),
        };
        let ty = |t: &hir::Ty| self.table.subst(&sub, &Ty::from_hir(t, None));
        let params = o.params.iter().map(|(m, t)| (*m, ty(t))).collect();
        let row = self.table.subst_row(&sub, &Row::from_hir(&o.row, None));
        (params, ty(&o.ret), row)
    }

    /// handlers.performing-operation: `Effect.op(…)` performs the operation: its effect, and its
    /// own row.
    pub(super) fn perform_op(
        &mut self,
        cx: &mut Cx,
        (at, callee_at): (TextRange, TextRange),
        effect: &Item,
        name: &Ident,
        args: &[Arg],
    ) -> tast::Expr {
        let Some(info) = self.env.decls.effect_info(effect) else {
            return self.give_up(cx, at, args);
        };
        let Some((_, o)) = info.op(&name.name) else {
            let message = format!("`{}` has no operation `{}`", effect.name, name.name);
            self.error(codes::E0314, name.at, message);
            return self.give_up(cx, at, args);
        };
        let targs = self.effect_args(cx, callee_at, effect, info);
        let (params, ret, mut row) = self.operation_sig(info, &targs, o);
        let args = self.arguments(cx, at, &params, &[], args);
        if row.effect(effect).is_none() {
            row.effects.insert(0, (effect.clone(), targs.clone()));
        }
        cx.perform(row.clone(), at);
        let callee = Callee::Operation(effect.clone(), name.name);
        node(tast::ExprKind::Call(callee, targs, args, row), ret, at)
    }

    /// handlers.performing-operation: an operation is performed by a call, and is no value.
    pub(super) fn operation_value(
        &mut self,
        at: TextRange,
        effect: &Item,
        name: &Ident,
    ) -> tast::Expr {
        let (e, n) = (&effect.name, &name.name);
        let message =
            format!("`{e}.{n}` is an operation, which is performed by a call: `{e}.{n}(…)`");
        self.error(codes::E0311, at, message);
        error_node(at)
    }

    /// handlers.handler-literals: whether the operation `f` implements is `o`, with its types: the
    /// same parameters, in the same modes, and the same result.
    fn implements(
        &mut self,
        args: &[Ty],
        info: &EffectInfo,
        o: &OperationSig,
        f: &HandlerOp,
    ) -> bool {
        let (params, ret, _) = self.operation_sig(info, args, o);
        if !f.plain || params.len() != f.params.len() {
            return false;
        }
        for ((m, t), (n, _, written)) in params.iter().zip(&f.params) {
            let w = self.of_hir(written);
            if m != n || !self.table.unify(&w, t) {
                return false;
            }
        }
        let written = f.ret.as_ref().map_or_else(Ty::unit, |r| self.of_hir(r));
        self.table.unify(&written, &ret)
    }

    /// handlers.handler-literals: the first operation that a literal misses, implements twice or
    /// with other types, or that the effect doesn't declare.
    fn mismatched(&mut self, args: &[Ty], info: &EffectInfo, ops: &[HandlerOp]) -> Option<String> {
        if let Some(o) = info
            .ops
            .iter()
            .find(|o| !ops.iter().any(|f| f.name.name == o.name))
        {
            return Some(format!("it misses the operation `{}`", o.name));
        }
        for f in ops {
            let n = f.name.name;
            let Some((_, o)) = info.op(&n) else {
                return Some(format!("the effect declares no operation `{n}`"));
            };
            if ops.iter().filter(|g| g.name.name == n).count() > 1 {
                return Some(format!("it implements `{n}` twice"));
            }
            if !self.implements(args, info, o, f) {
                return Some(format!("its `{n}` has other types than the effect's"));
            }
        }
        None
    }

    /// handlers.handler-literals and handlers.resuming: an operation's body, as a closure literal
    /// of the function that writes the handler. Its effects are its operation's row's, and what the
    /// handler's row `hrow` holds. One that takes control, with `answer`, has the type `R`, and may
    /// `resume`.
    fn handler_op(
        &mut self,
        (answer, hrow): (Option<&Ty>, &Row),
        (info, args): (&EffectInfo, &[Ty]),
        f: &HandlerOp,
    ) -> (hir::Name, tast::Expr) {
        let (_, o) = info
            .op(&f.name.name)
            .expect("a matching literal implements its operations");
        let (params, ret, row) = self.operation_sig(info, args, o);
        let patterns = f
            .params
            .iter()
            .zip(&params)
            .map(|((_, v, written), (_, t))| {
                self.locals.insert(*v, t.clone());
                tast::Pat {
                    kind: tast::PatKind::Bind(*v),
                    ty: t.clone(),
                    at: written.at,
                }
            })
            .collect();
        let body_ty = answer.cloned().unwrap_or_else(|| ret.clone());
        let mut inner = Cx::new(body_ty.clone());
        self.enter_regions(&mut inner);
        inner.known.clone_from(&row.effects);
        inner.resume = answer.map(|r| (ret, r.clone()));
        let (b, _) = self.block_expr(&mut inner, f.name.at, Some(&body_ty), &f.body);
        let fits = Row {
            tail: hrow.tail.clone(),
            ..row
        };
        self.settle(&inner.effects, &fits, false);
        let body = node(tast::ExprKind::Block(b), body_ty.clone(), f.name.at);
        let closure = tast::ExprKind::Closure(patterns, Box::new(body));
        let ty = Ty::func(params, body_ty, fits);
        (f.name.name, node(closure, ty, f.name.at))
    }

    /// handlers.handler-literals: the literal of a handler of `effect`, whose arguments the literal
    /// writes or inference gives, as the expected type does. Its row holds what its bodies perform
    /// beyond their operations' rows: `io`, and its own effect, which they perform on the handler
    /// outside it (handlers.with). Anything else is E0502 in the body.
    fn handler_of(
        &mut self,
        (expected, at): (Option<&Ty>, TextRange),
        h: &HandlerLit,
        inst: &hir::EffectInst,
        info: &EffectInfo,
    ) -> tast::Expr {
        let args: Vec<Ty> = if inst.args.is_empty() {
            info.params
                .iter()
                .map(|_| self.fresh(h.effect_at))
                .collect()
        } else {
            let self_ty = self.env.self_ty.clone();
            inst.args
                .iter()
                .map(|a| Ty::from_hir(a, self_ty.as_ref()))
                .collect()
        };
        let answer = h.answer.as_ref().map(|r| self.of_hir(r));
        if let Some(Ty::Handler(e)) = expected.map(|t| self.resolved(t))
            && e.effect == inst.effect
        {
            self.table.unify_all(&args, &e.args);
        }
        if let Some(why) = self.mismatched(&args, info, &h.ops) {
            let message = format!("this handler doesn't match `{}`: {why}", inst.effect.name);
            self.error(codes::E0511, h.effect_at, message);
            return error_node(at);
        }
        let hrow = self.table.fresh_row(true);
        if let Some(rv) = self.table.open_var(&hrow) {
            let bound = Row {
                io: true,
                effects: vec![(inst.effect.clone(), args.clone())],
                ..Row::EMPTY
            };
            self.table.add_upper(rv, (bound, Handled::Nothing));
        }
        let ops = h
            .ops
            .iter()
            .map(|f| self.handler_op((answer.as_ref(), &hrow), (info, &args), f))
            .collect();
        let lit = tast::HandlerExpr {
            effect: inst.effect.clone(),
            control: answer.is_some(),
            ops,
        };
        let ty = Ty::Handler(Box::new(HandlerTy {
            effect: inst.effect.clone(),
            args,
            answer,
            row: hrow,
        }));
        node(tast::ExprKind::Handler(Box::new(lit)), ty, at)
    }

    pub(super) fn handler_lit(
        &mut self,
        expected: Option<&Ty>,
        at: TextRange,
        h: &HandlerLit,
    ) -> tast::Expr {
        if h.is_async {
            // tasks.async
            let message = "`async` is handled by `task.threads()` or `task.sequential()`, which \
                           start tasks; a handler literal can't";
            self.error(codes::E0511, h.effect_at, message.to_owned());
            return error_node(at);
        }
        let decls = self.env.decls;
        if let Some((inst, Some(info))) =
            h.effect.as_ref().map(|i| (i, decls.effect_info(&i.effect)))
        {
            return self.handler_of((expected, at), h, inst, info);
        }
        self.broken = true;
        error_node(at)
    }

    /// handlers.resuming: `resume(v)`, in an operation's body of a handler that takes control, and
    /// E0513 anywhere else.
    pub(super) fn resume_expr(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        value: Option<&hir::Expr>,
    ) -> tast::Expr {
        let Some((op_ret, answer)) = cx.resume.clone() else {
            let message = "`resume` belongs in an operation of a handler that takes control, \
                           written `handler E -> R { … }`";
            self.error(codes::E0513, at, message.to_owned());
            if let Some(v) = value {
                self.abandon(cx, v);
            }
            return error_node(at);
        };
        if value.is_none() {
            self.expect(at, &op_ret, &Ty::unit());
        }
        let v = value.map(|e| Box::new(self.check(cx, &op_ret, e)));
        node(tast::ExprKind::Resume(v), answer, at)
    }
}
