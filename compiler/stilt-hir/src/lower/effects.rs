//! Effects and handlers (handlers.declaring-effect; tasks.async): an effect's declaration, the
//! effects of rows and handler types, and the handler literals, `with` and `resume` of bodies.

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::ast::{self, AstNode};
use stilt_syntax::{TextRange, TextSize};

use super::patterns::Binder;
use super::poly::Spot;
use super::{Ctx, Meaning, Resolver, dotted};
use crate::hir::{
    DeclKind, EffectDecl, EffectInst, ExprKind, GenericId, HandlerLit, HandlerOp, HandlerTy, Held,
    Ident, Item, Mode, Name, Operation, Owner, Row, Ty,
};
use crate::scope::{Kind, Namespace};

impl Resolver<'_> {
    /// handlers.declaring-effect: an effect, whose type parameters are in scope in its operations,
    /// of which there is at least one (E0518), each named once (E0208) and taking no `self`
    /// (E0215).
    pub(super) fn effect_kind(&mut self, e: &ast::Effect, owner: &Owner) -> DeclKind {
        DeclKind::Effect(self.effect_decl(e, e.is_pub(), owner))
    }

    fn effect_decl(&mut self, e: &ast::Effect, public: bool, owner: &Owner) -> EffectDecl {
        let name = self.name(e.name(), e.syntax());
        let mut ctx = Ctx {
            public,
            ..Ctx::module()
        };
        let mut params = Vec::new();
        for (index, p) in (0..).zip(e.params()) {
            let n = self.name(p.name(), p.syntax());
            let id = GenericId {
                owner: owner.clone(),
                index,
            };
            self.declare(&mut ctx.type_params, "a type parameter", &n, id);
            params.push(n.name);
        }
        let ops: Vec<ast::Operation> = e.operations().collect();
        if ops.is_empty() {
            let message = format!(
                "the effect `{}` declares no operation, so nothing can perform it",
                name.name
            );
            self.error(codes::E0518, name.at, message);
        }
        let names: Vec<Ident> = ops
            .iter()
            .map(|o| self.name(o.name(), o.syntax()))
            .collect();
        self.check_unique("an operation", &names);
        let ops = ops
            .iter()
            .zip(names)
            .map(|(o, n)| self.operation(&ctx, o, n.name))
            .collect();
        EffectDecl {
            name: name.name,
            params,
            ops,
        }
    }

    /// A function's own row, where `main`'s holds no user-defined effect
    /// (handlers.no-effect-reaches-main).
    pub(super) fn fn_row(&mut self, signature: &Ctx, f: &ast::Fn) -> Row {
        self.main_row = !self.module.std
            && &*self.module.name == "main"
            && f.name().is_some_and(|n| n.text() == "main");
        let row = self.row(signature, f.row());
        self.main_row = false;
        row
    }

    /// E0215 for an operation's receiver, which only functions of impl and trait blocks take.
    fn no_receiver(&mut self, list: Option<&ast::ParamList>) {
        if let Some(s) = list.and_then(ast::ParamList::self_param) {
            let at = s
                .self_token()
                .map_or_else(|| self.at(s.syntax()), |t| self.at_token(&t));
            let message = "an operation takes no `self`, since no value performs it".to_owned();
            self.error(codes::E0215, at, message);
        }
    }

    /// handlers.no-inout-parameter: E0517 for an operation's parameter `p`, named `n`, marked
    /// `inout`, which is then taken by value, so that a handler's operation that marks one is no
    /// mismatch as well. Where `result` is the end of the parameters of an operation without a
    /// result, the fix takes the parameter by value and returns its type.
    fn by_value(&mut self, p: &ast::Param, n: &Ident, result: Option<TextSize>) -> Mode {
        let Some(inout) = p.inout_token().filter(|_| p.mode() == Mode::Inout) else {
            return Mode::Let;
        };
        let message = format!(
            "an operation takes `{}` by value, not `inout`: take it and return the new value",
            n.name
        );
        let mut d = Diagnostic::new(codes::E0517, n.at, message);
        if let (Some(end), Some(ty)) = (result, p.ty()) {
            let mark = TextRange::new(self.at_token(&inout).start(), n.at.start());
            let edits = vec![
                Edit::delete(mark),
                Edit::insert(end, format!(" -> {}", ty.syntax().text())),
            ];
            let title = format!("take `{}` by value and return its new value", n.name);
            d = d.with_fix(Fix::new(title, edits));
        }
        self.diagnostics.push(d);
        Mode::Let
    }

    fn operation(&mut self, ctx: &Ctx, o: &ast::Operation, name: Name) -> Operation {
        self.no_receiver(o.param_list().as_ref());
        // Its parameters' names are bound, so that one written twice is E0208, as a function's.
        let frame = self.enter_body();
        let mut b = Binder::default();
        // The fix returns the parameter's new value when nothing else is returned.
        let inouts = o.params().filter(|p| p.mode() == Mode::Inout).count();
        let result = o
            .param_list()
            .filter(|_| o.ret_type().is_none() && inouts == 1)
            .map(|l| self.at(l.syntax()).end());
        let params = o
            .params()
            .map(|p| {
                let t = self.ty_in(ctx, p.ty(), Spot::Param);
                let n = self.name(p.name(), p.syntax());
                self.bind(&mut b, &n);
                (self.by_value(&p, &n, result), t)
            })
            .collect();
        self.leave_body(frame);
        let ret = o.ret_type().map(|r| self.ty(ctx, r.ty()));
        let row = self.row(ctx, o.row());
        Operation {
            name,
            params,
            ret,
            row,
        }
    }

    /// handlers.effects-in-rows and handlers.performing-operation: the effect that `path` names,
    /// with its type arguments, or `None` after an error: a name that is no effect (E0212), or the
    /// wrong number of arguments (E0300).
    pub(super) fn named_effect(
        &mut self,
        ctx: &Ctx,
        path: &[Ident],
        args: impl Iterator<Item = ast::Type>,
    ) -> Option<EffectInst> {
        let first = path.first()?;
        match self.walk_to_end(ctx, Namespace::Types, "an effect", path) {
            (Meaning::Broken, _) => None,
            (Meaning::Item(item, entry), _) if entry.kind == Kind::Effect => {
                self.check_public(ctx, first.at, &item, entry);
                let args: Vec<Ty> = args
                    .map(|a| self.ty_in(ctx, Some(a), Spot::TypeArg))
                    .collect();
                let given = u32::try_from(args.len()).unwrap_or(u32::MAX);
                if given == entry.arity {
                    return Some(EffectInst { effect: item, args });
                }
                let message = format!(
                    "`{}` takes {} type argument{}, not {given}",
                    dotted(path),
                    entry.arity,
                    if entry.arity == 1 { "" } else { "s" }
                );
                self.error(codes::E0300, first.at, message);
                None
            }
            (m, last) => {
                self.wrong_kind(&path[last], &m, "an effect");
                None
            }
        }
    }

    /// The effect a handler type or literal names, and where it is written.
    fn effect_ref(&mut self, ctx: &Ctx, e: &ast::EffectRef) -> (Option<EffectInst>, TextRange) {
        match e {
            ast::EffectRef::Async(a) => {
                let effect = EffectInst {
                    effect: Item::async_effect(),
                    args: Vec::new(),
                };
                (Some(effect), self.at(a.syntax()))
            }
            ast::EffectRef::Named(n) => {
                let path = self.path(n.path());
                let at = path.first().map_or_else(|| self.at(n.syntax()), |f| f.at);
                (self.named_effect(ctx, &path, n.args()), at)
            }
        }
    }

    /// handlers.effects-in-rows: adds an effect to a row, which holds one instance of each (E0515,
    /// at the second).
    pub(super) fn add_effect(&mut self, r: &mut Row, e: EffectInst, at: TextRange) {
        if r.effects.iter().any(|f| f.effect == e.effect) {
            let message = format!(
                "`{}` is already in this row, which holds one instance of an effect",
                e.effect.name
            );
            self.error(codes::E0515, at, message);
        } else {
            r.effects.push(e);
        }
    }

    /// An effect written in a row, `Name` or `Name<T…>` (handlers.effects-in-rows).
    pub(super) fn row_effect(&mut self, ctx: &Ctx, r: &mut Row, e: &ast::RowEffect) {
        let path = self.path(e.path());
        let Some(first) = path.first().map(|f| f.at) else {
            return;
        };
        if let Some(found) = self.named_effect(ctx, &path, e.args()) {
            // handlers.no-effect-reaches-main: no user-defined effect reaches `main`, whose row may
            // hold `async` (handlers.no-effect-reaches-main).
            if self.main_row {
                let message = format!(
                    "`main` handles `{}` with `with`, so its row can't hold it",
                    found.effect.name
                );
                self.error(codes::E0512, first, message);
            }
            self.add_effect(r, found, first);
        }
    }

    /// `async` written in a row (tasks.async).
    pub(super) fn row_async(&mut self, r: &mut Row, a: &ast::RowAsync) {
        let at = self.at(a.syntax());
        let effect = EffectInst {
            effect: Item::async_effect(),
            args: Vec::new(),
        };
        self.add_effect(r, effect, at);
    }

    /// handlers.handler-types: a handler's type, or the error type when its effect has an error.
    pub(super) fn handler_type(&mut self, ctx: &Ctx, h: &ast::HandlerType) -> Ty {
        let Some(e) = h.effect() else {
            return Ty::Error;
        };
        let (Some(effect), _) = self.effect_ref(ctx, &e) else {
            return Ty::Error;
        };
        let answer = h.answer().map(|r| self.ty(ctx, r.ty()));
        let row = self.row(ctx, h.row());
        Ty::Handler(Box::new(HandlerTy {
            effect,
            answer,
            row,
        }))
    }

    /// handlers.handler-literals; tasks.async: a handler literal, whose effect is named, or is
    /// `async`, which type checking reports (E0511).
    pub(super) fn handler_expr(&mut self, ctx: &Ctx, h: &ast::HandlerExpr) -> ExprKind {
        let (effect, effect_at, is_async) = match h.effect() {
            Some(ast::EffectRef::Async(_)) => (None, self.first_token(h.syntax()), true),
            Some(e) => {
                let (effect, at) = self.effect_ref(ctx, &e);
                (effect, at, false)
            }
            None => (None, self.first_token(h.syntax()), false),
        };
        let answer = h
            .answer()
            .and_then(|r| r.ty())
            .map(|t| self.type_ref(ctx, t, Spot::Other));
        let ops = h.fns().map(|f| self.handler_op(ctx, &f)).collect();
        ExprKind::Handler(Box::new(HandlerLit {
            effect,
            effect_at,
            is_async,
            answer,
            ops,
        }))
    }

    /// An operation of a handler literal, written as a function, whose parameters its body binds
    /// and in whose body no loop is open.
    fn handler_op(&mut self, ctx: &Ctx, f: &ast::Fn) -> HandlerOp {
        let name = self.name(f.name(), f.syntax());
        let mut b = Binder::default();
        let list = f.param_list();
        self.no_receiver(list.as_ref());
        let params = list
            .iter()
            .flat_map(ast::ParamList::params)
            .map(|p| {
                let t = match p.ty() {
                    Some(t) => self.type_ref(ctx, t, Spot::Param),
                    None => crate::hir::TypeRef {
                        ty: Ty::Error,
                        at: self.at(p.syntax()),
                    },
                };
                let n = self.name(p.name(), p.syntax());
                (self.by_value(&p, &n, None), self.bind(&mut b, &n), t)
            })
            .collect();
        let plain = f.generic_list().is_none()
            && !f.ret_type().is_some_and(|r| r.is_inout())
            && f.where_clause().is_none()
            && f.limits().is_none()
            && list.and_then(|l| l.self_param()).is_none();
        let depth = self.scope.len();
        self.bring_into_scope(&b);
        let inner = Ctx {
            in_loop: false,
            ..ctx.clone()
        };
        let body = match f.body() {
            Some(ast::FnBody::Block(block)) => self.block(&inner, Some(block)),
            Some(ast::FnBody::HoleBody(hole)) => vec![self.hole_stmt(&hole)],
            None => Vec::new(),
        };
        self.scope.truncate(depth);
        let ret = f
            .ret_type()
            .and_then(|r| r.ty())
            .map(|t| self.type_ref(ctx, t, Spot::Other));
        let row = self.row(ctx, f.row());
        HandlerOp {
            name,
            params,
            ret,
            row,
            plain,
            body,
        }
    }

    /// The statement of a body written `= ?`: the hole, at the `?`.
    fn hole_stmt(&self, hole: &ast::HoleBody) -> crate::hir::Stmt {
        let at = self.at(hole.syntax());
        let at = TextRange::new(at.end() - stilt_syntax::TextSize::from(1), at.end());
        crate::hir::Stmt {
            kind: crate::hir::StmtKind::Expr(crate::hir::Expr {
                kind: ExprKind::Hole,
                at,
            }),
            at,
        }
    }

    /// `with h₁, h₂ { … }` (handlers.with) and `resume(v)` (handlers.resuming).
    pub(super) fn with_expr(&mut self, ctx: &Ctx, w: &ast::WithExpr) -> ExprKind {
        let handlers = w.handlers().map(|h| self.expr(ctx, &h)).collect();
        ExprKind::With(handlers, self.block(ctx, w.body()))
    }

    /// `when a, b { … }` (shared.when): each name a local or a parameter, named once
    /// (E0433), and in the block a local of its own, the place of the value its handle
    /// reaches. Whether a handle's type is `Shared<T>` is for type checking.
    pub(super) fn when_expr(&mut self, ctx: &Ctx, w: &ast::WhenExpr) -> ExprKind {
        let mut b = Binder::default();
        let mut held: Vec<Held> = Vec::new();
        let mut named = Vec::new();
        for n in w.names() {
            let Some(token) = n.ident() else { continue };
            let name = self.ident(&token);
            let handle = self.expr(ctx, &ast::Expr::NameRef(n));
            let place = match handle.kind {
                ExprKind::Local(v) if held.iter().any(|h| h.handle.kind == ExprKind::Local(v)) => {
                    let message = format!("`{}` is named twice in this `when`", name.name);
                    self.error(codes::E0433, name.at, message);
                    self.fresh(&name)
                }
                // A name that resolves to nothing is reported where it is unknown, so a second
                // one is no `when` of its own to report (errors.error-type).
                ExprKind::Error if named.contains(&name.name) => self.fresh(&name),
                ExprKind::Local(_) | ExprKind::Error => self.bind(&mut b, &name),
                _ => {
                    let message = format!(
                        "`{}` isn't a local binding or a parameter, so `when` can't hold it",
                        name.name
                    );
                    self.error(codes::E0433, name.at, message);
                    self.bind(&mut b, &name)
                }
            };
            named.push(name.name);
            held.push(Held { handle, place });
        }
        let depth = self.scope.len();
        self.bring_into_scope(&b);
        let body = self.block(ctx, w.body());
        self.scope.truncate(depth);
        ExprKind::When(held, body)
    }

    pub(super) fn resume_expr(&mut self, ctx: &Ctx, r: &ast::ResumeExpr) -> ExprKind {
        ExprKind::Resume(r.expr().map(|e| Box::new(self.expr(ctx, &e))))
    }
}
