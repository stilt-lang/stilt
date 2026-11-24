//! Declarations: functions, constants, types, traits and impl blocks
//! (declarations.function-declarations, declarations.constant-declarations and
//! declarations.records; traits.impl-blocks and traits.declaring-trait).

use std::collections::HashSet;
use stilt_diag::codes;

use stilt_syntax::ast::{self, AstNode};
use stilt_syntax::text::string_value;
use stilt_syntax::{SyntaxKind, TextRange};

use super::bodies::Frame;
use super::bounds::GenericsOf;
use super::limits::implicit;
use super::patterns::Binder;
use super::poly::Spot;
use super::records::Hidden;
use super::views;
use super::{Ctx, Resolver};
use crate::hir::{
    Body, BodyIndex, BodyValue, ConstDecl, Decl, DeclId, DeclKind, Expr, ExprKind, FnBody, FnDecl,
    Ident, Limit, LocalId, Member, MemberKind, Name, Owner, Param, SignatureSpans, Stmt, StmtKind,
    Ty,
};
use crate::scope::is_primitive;

impl Resolver<'_> {
    /// lexical.primitive-type-names.
    pub(super) fn check_not_primitive(&mut self, n: &Ident) {
        if is_primitive(&n.name) {
            let message = format!("`{}` is a primitive type name", n.name);
            self.error(codes::E0210, n.at, message);
        }
    }

    /// Reports each name that an earlier one repeats, for names declared together inside a
    /// declaration.
    pub(super) fn check_unique<'n>(
        &mut self,
        what: &str,
        names: impl IntoIterator<Item = &'n Ident>,
    ) {
        let mut seen = HashSet::new();
        for n in names {
            if !seen.insert(n.name) {
                let message = format!("`{}` is already {what} here", n.name);
                self.error(codes::E0208, n.at, message);
            }
        }
    }

    pub(super) fn function(
        &mut self,
        ctx: &Ctx,
        f: &ast::Fn,
        public: bool,
        methods: bool,
        owner: &Owner,
    ) -> FnDecl {
        let name = self.name(f.name(), f.syntax());
        self.own_polys(owner);
        let mut signature = Ctx {
            public,
            assumed: Vec::new(),
            fixed: Vec::new(),
            ..ctx.clone()
        };
        let generics = self.generics(
            &mut signature,
            (f.generic_list(), f.where_clause()),
            owner,
            GenericsOf::Function,
        );
        // No binding of the function takes a value parameter's name
        // (generics.value-parameters-in-body).
        let names = signature.value_params.iter().map(|(n, ..)| *n).collect();
        let outer = std::mem::replace(&mut self.values_in_scope, names);
        let frame = self.enter_body();
        let at = f.name().map_or_else(
            || f.syntax().text_range().start(),
            |n| n.syntax().text_range().end(),
        );
        self.hidden = Some(Hidden::of(f, owner, generics.len(), at));
        let params = self.params(&signature, f.param_list(), methods);
        let (ret, projection, row) = self.result(&signature, f);
        self.check_determined((&signature, f), owner, &params.declared, ret.as_ref());
        let mut generics = generics;
        generics.extend(self.hidden.take().map(|h| h.made).unwrap_or_default());
        let kept = f.limits().map(|c| self.clause(&c)).unwrap_or_default();
        let unknown = crate::items::only_named(f.syntax());
        let mut decl = FnDecl {
            name: name.name,
            generics,
            params: params.declared.clone(),
            ret: if unknown { Some(Ty::Error) } else { ret },
            projection,
            row,
            limits: implicit(&kept),
            assumed: std::mem::take(&mut signature.assumed),
            body: None,
            procedural: f.is_macro(),
            foreign: f.is_foreign(),
        };
        if f.is_macro() {
            self.check_macro(f, &decl);
        }
        if recovered(f.syntax()) {
            self.values_in_scope = outer;
            return self.recovered_function(frame, decl, name.at, kept);
        }
        decl.body = self.function_body(f, signature, (frame, &params), name.at, kept);
        self.values_in_scope = outer;
        decl
    }

    /// The body of a function, its block or its hole, lowered in the frame of its parameters.
    fn function_body(
        &mut self,
        f: &ast::Fn,
        signature: Ctx,
        (frame, params): (Frame, &Params),
        at: TextRange,
        kept: Vec<(Limit, TextRange)>,
    ) -> Option<FnBody> {
        match f.body() {
            Some(ast::FnBody::Block(block)) => {
                let inner = Ctx {
                    public: false,
                    ..signature
                };
                let spans = self.signature_spans(f);
                let body = self.fn_body(&inner, frame, params, block, (at, spans, kept));
                Some(FnBody::Block(body))
            }
            Some(ast::FnBody::HoleBody(hole)) => {
                self.leave_body(frame);
                Some(FnBody::Hole(self.hole_body(&hole, at, kept)))
            }
            None => {
                self.leave_body(frame);
                None
            }
        }
    }

    /// A function's result type, whether it is a projection's (projections.declaring-projection),
    /// and its row.
    fn result(&mut self, signature: &Ctx, f: &ast::Fn) -> (Option<Ty>, bool, crate::hir::Row) {
        let ret = f.ret_type().map(|r| {
            let t = self.ty_in(signature, r.ty(), Spot::Result);
            self.checked_view(t, r.ty().as_ref(), views::Free)
        });
        let projection = f.ret_type().is_some_and(|r| r.is_inout());
        let row = self.fn_row(signature, f);
        let row = self.checked_row(row, f.row());
        let row = if projection {
            self.projection_row(row, f.row())
        } else {
            row
        };
        (ret, projection, row)
    }

    /// A function that a part with a syntax error declares (program.errors-outside-bodies), `decl`
    /// with a body that is an error, reported at `at` under the limits `limits`. Without its
    /// parameters, its signature is unknown, and its return type is the error type, so that every
    /// use of it is an error.
    fn recovered_function(
        &mut self,
        frame: Frame,
        mut decl: FnDecl,
        at: TextRange,
        limits: Vec<(Limit, TextRange)>,
    ) -> FnDecl {
        self.leave_body(frame);
        let value = BodyValue::Block(vec![Stmt {
            kind: StmtKind::Expr(Expr {
                kind: ExprKind::Error,
                at,
            }),
            at,
        }]);
        let body = self.add_body(Body {
            locals: Vec::new(),
            params: Vec::new(),
            value,
            at,
            has_errors: true,
            signature: None,
            limits,
            held: Vec::new(),
            analysed: Vec::new(),
            fixed: Vec::new(),
            expansions: Vec::new(),
            unsafe_blocks: Vec::new(),
        });
        decl.body = Some(FnBody::Block(body));
        decl
    }

    /// A function's parameters, whose names its body binds.
    fn params(&mut self, signature: &Ctx, list: Option<ast::ParamList>, methods: bool) -> Params {
        let mut params = Params::default();
        let Some(list) = list else { return params };
        if let Some(s) = list.self_param() {
            let at = self.at(s.syntax());
            if !methods {
                // The error is at the `self` itself, after any `inout` (traits.methods; E0215's
                // span).
                let keyword = s.self_token().map_or(at, |t| self.at_token(&t));
                let message = "only functions in impl and trait blocks take `self`";
                self.error(codes::E0215, keyword, message.to_owned());
            }
            let written = self.receiver_type(signature, &s);
            let n = Ident {
                name: Name::from("self"),
                at,
            };
            let v = self.fresh(&n);
            params.binder.bound.push((n.name, v));
            params.locals.push(v);
            params.declared.push(Param::SelfParam(s.mode(), written));
        }
        for p in list.params() {
            let t = if self.row_variable_on_passing(&p) {
                Ty::Error
            } else {
                let t = self.ty_in(signature, p.ty(), Spot::OwnParam);
                self.checked_view(t, p.ty().as_ref(), views::Free)
            };
            let n = self.name(p.name(), p.syntax());
            params.locals.push(self.bind(&mut params.binder, &n));
            params
                .declared
                .push(Param::Param(p.mode(), t, p.is_escaping()));
        }
        params
    }

    /// A function's block, with its parameters in scope. Only the errors in the block make the
    /// body one with errors. It is reported at `at`, its signature has the spans `spans`, and
    /// its `without` keeps the limits `limits`.
    fn fn_body(
        &mut self,
        ctx: &Ctx,
        frame: Frame,
        params: &Params,
        block: ast::Block,
        (at, spans, limits): (TextRange, SignatureSpans, Vec<(Limit, TextRange)>),
    ) -> BodyIndex {
        let before = self.diagnostics.len();
        self.bring_into_scope(&params.binder);
        let spans = SignatureSpans {
            end: self.at(block.syntax()).end(),
            ..spans
        };
        let (block, held, analysed) = self.body_code(|this| this.block(ctx, Some(block)));
        let has_errors = self.diagnostics.len() > before || !held.is_empty();
        let locals = self.leave_body(frame);
        self.add_body(Body {
            locals,
            params: params.locals.clone(),
            value: BodyValue::Block(block),
            at,
            has_errors,
            signature: Some(spans),
            limits,
            held,
            analysed,
            fixed: ctx.fixed.clone(),
            expansions: Vec::new(),
            unsafe_blocks: Vec::new(),
        })
    }

    /// The body of `= ?`: the hole, at the `?`, under the limits `limits`.
    fn hole_body(
        &mut self,
        hole: &ast::HoleBody,
        at: TextRange,
        limits: Vec<(Limit, TextRange)>,
    ) -> BodyIndex {
        let question = hole
            .syntax()
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .find(|t| t.kind() == SyntaxKind::QUESTION)
            .map_or_else(|| self.at(hole.syntax()), |t| self.at_token(&t));
        let value = BodyValue::Expr(Expr {
            kind: ExprKind::Hole,
            at: question,
        });
        self.add_body(Body {
            locals: Vec::new(),
            params: Vec::new(),
            value,
            at,
            has_errors: false,
            signature: None,
            limits,
            held: Vec::new(),
            analysed: Vec::new(),
            fixed: Vec::new(),
            expansions: Vec::new(),
            unsafe_blocks: Vec::new(),
        })
    }

    pub(super) fn constant(&mut self, ctx: &Ctx, c: &ast::Const, public: bool) -> ConstDecl {
        let name = self.name(c.name(), c.syntax());
        let signature = Ctx {
            public,
            ..ctx.clone()
        };
        let ty = self.ty_in(&signature, c.ty(), Spot::Constant);
        let ty = self.checked_view(ty, c.ty().as_ref(), views::Constant);
        let value = self.body(name.at, |this| {
            BodyValue::Expr(this.opt_expr(ctx, c.value()))
        });
        ConstDecl {
            name: name.name,
            ty,
            value,
        }
    }

    /// A member of an impl block or trait: the grammar puts only functions and constants there.
    pub(super) fn member(
        &mut self,
        ctx: &Ctx,
        item: &ast::Item,
        public: bool,
        owner: &Owner,
    ) -> Member {
        let unknown = crate::items::only_named(item.syntax());
        let (is_pub, kind, docs) = match item {
            ast::Item::Fn(f) => (
                f.is_pub(),
                MemberKind::Fn(self.function(ctx, f, public, true, owner)),
                f.docs(),
            ),
            ast::Item::Const(c) => (
                c.is_pub(),
                MemberKind::Const(self.constant(ctx, c, public)),
                c.docs(),
            ),
            _ => unreachable!("an impl block or trait holds only functions and constants"),
        };
        Member {
            is_pub,
            kind,
            unknown,
            examples: self.examples(docs),
        }
    }

    pub(super) fn decl(&mut self, item: &ast::Item, id: &DeclId) -> Decl {
        let ctx = Ctx::module();
        let owner = Owner {
            decl: id.clone(),
            member: None,
        };
        self.own_polys(&owner);
        let (is_pub, kind, docs) = match item {
            ast::Item::Fn(f) => {
                let decl = self.function(&ctx, f, f.is_pub(), false, &owner);
                (f.is_pub(), DeclKind::Fn(decl), f.docs())
            }
            ast::Item::TypeDecl(t) => {
                let decl = self.type_decl(&ctx, t, t.is_pub(), &owner);
                (t.is_pub(), DeclKind::Type(decl), t.docs())
            }
            ast::Item::Trait(t) => (t.is_pub(), self.trait_decl(t, id), t.docs()),
            ast::Item::Const(c) => {
                let decl = self.constant(&ctx, c, c.is_pub());
                (c.is_pub(), DeclKind::Const(decl), c.docs())
            }
            ast::Item::Test(t) => {
                let name = t.name().map(|n| string_value(&n)).unwrap_or_default();
                let at = self.first_token(t.syntax());
                let body = self.body(at, |this| BodyValue::Block(this.block(&ctx, t.body())));
                (false, DeclKind::Test(name, body), t.docs())
            }
            ast::Item::Syntax(s) => (s.is_pub(), DeclKind::Macro(self.macro_decl(s)), s.docs()),
            ast::Item::Effect(e) => (e.is_pub(), self.effect_kind(e, &owner), e.docs()),
            ast::Item::Use(_) | ast::Item::Impl(_) => {
                unreachable!("uses and impl blocks aren't declarations")
            }
        };
        Decl {
            is_pub,
            kind,
            examples: self.examples(docs),
        }
    }
}

pub(super) fn declared_name(item: &ast::Item) -> Option<ast::Name> {
    match item {
        ast::Item::Fn(f) => f.name(),
        ast::Item::TypeDecl(t) => t.name(),
        ast::Item::Trait(t) => t.name(),
        ast::Item::Const(c) => c.name(),
        ast::Item::Syntax(s) => s.name(),
        ast::Item::Effect(e) => e.name(),
        ast::Item::Test(_) | ast::Item::Use(_) | ast::Item::Impl(_) => None,
    }
}

/// Whether a part with a syntax error declares the item of `node`, which then holds the
/// tokens the part drops in an error node (program.errors-outside-bodies).
pub(super) fn recovered(node: &stilt_syntax::SyntaxNode) -> bool {
    node.children().any(|c| c.kind() == SyntaxKind::ERROR)
}

/// A function's parameters: the names they bind, their locals, and their modes and types.
#[derive(Default)]
struct Params {
    binder: Binder,
    locals: Vec<LocalId>,
    declared: Vec<Param>,
}
