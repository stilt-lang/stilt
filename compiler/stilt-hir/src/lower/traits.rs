//! Traits (traits.declaring-trait; traits.trait-parameters, traits.trait-constants and
//! traits.constructor-traits): their parameters, functions and constants, and the receivers of the
//! methods of constructor traits.

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::ast::{self, AstNode};
use stilt_syntax::{SyntaxKind, TextRange};

use super::views;
use super::{Ctx, Resolver, SelfKind};
use crate::hir::{
    BodyValue, DeclId, DeclKind, GenericId, Ident, Member, MemberKind, Owner, TraitDecl, Ty,
};
use crate::items::TraitShape;

impl Resolver<'_> {
    /// A trait: its parameters, its functions and its constants (traits.declaring-trait;
    /// traits.trait-parameters, traits.trait-constants and traits.constructor-traits, ).
    pub(super) fn trait_decl(&mut self, t: &ast::Trait, id: &DeclId) -> DeclKind {
        let shape = TraitShape::of(t);
        let members: Vec<ast::Item> = t.members().collect();
        let names: Vec<_> = members.iter().map(|m| self.member_name(m)).collect();
        for n in &names {
            self.check_not_primitive(n);
        }
        self.check_unique("a member of this trait", &names);
        let mut ctx = Ctx {
            self_kind: SelfKind::Trait(shape.arity),
            constructor: shape.arity,
            trait_member: true,
            ..Ctx::module()
        };
        let owner = Owner {
            decl: id.clone(),
            member: None,
        };
        let mut params = Vec::new();
        let written: Vec<ast::Generic> = t.params().map(ast::Generic::TypeParam).collect();
        let _ = self.check_packs(&written, true);
        for (index, p) in (0..).zip(t.params()) {
            let n = self.name(p.name(), p.syntax());
            self.check_not_primitive(&n);
            let id = GenericId {
                owner: owner.clone(),
                index,
            };
            self.declare(&mut ctx.type_params, "a parameter of this trait", &n, id);
            params.push(n.name);
        }
        let members = (0..)
            .zip(&members)
            .map(|(j, m)| {
                let owner = Owner {
                    decl: id.clone(),
                    member: Some(j),
                };
                match m {
                    ast::Item::Const(c) => self.trait_const(&ctx, c, t.is_pub()),
                    _ => self.member(&ctx, m, t.is_pub(), &owner),
                }
            })
            .collect();
        DeclKind::Trait(TraitDecl {
            name: self.name(t.name(), t.syntax()).name,
            params,
            arity: shape.arity,
            members,
        })
    }

    /// The name of a member of a trait or an impl block.
    pub(super) fn member_name(&self, m: &ast::Item) -> Ident {
        match m {
            ast::Item::Fn(f) => self.name(f.name(), f.syntax()),
            ast::Item::Const(c) => self.name(c.name(), c.syntax()),
            other => self.name(None, other.syntax()),
        }
    }

    /// A constant of a trait, with its default if it has one (traits.trait-constants).
    fn trait_const(&mut self, ctx: &Ctx, c: &ast::Const, public: bool) -> Member {
        let name = self.name(c.name(), c.syntax());
        let signature = Ctx {
            public,
            ..ctx.clone()
        };
        let ty = self.ty(&signature, c.ty());
        let ty = self.checked_view(ty, c.ty().as_ref(), views::Constant);
        // A constant whose part breaks after its `=` has a default with an error, so no impl
        // lacks it (errors.broken-parts).
        let broken_value = c.value().is_none()
            && c.syntax().children().any(|n| {
                n.kind() == SyntaxKind::ERROR
                    && n.first_token().is_some_and(|t| t.kind() == SyntaxKind::EQ)
            });
        let value = c
            .value()
            .map(|v| self.body(name.at, |this| BodyValue::Expr(this.opt_expr(ctx, Some(v)))))
            .or_else(|| {
                broken_value
                    .then(|| self.body(name.at, |this| BodyValue::Expr(this.opt_expr(ctx, None))))
            });
        Member {
            is_pub: public,
            kind: MemberKind::TraitConst(name.name, ty, value),
            unknown: crate::items::only_named(c.syntax()),
            examples: self.examples(c.docs()),
        }
    }

    /// The written type of a receiver (traits.receiver-types): a constructor trait's methods, and
    /// its impls', write it, as `self: Self<A>`, and no other receiver does, its type being `Self`.
    pub(super) fn receiver_type(&mut self, ctx: &Ctx, s: &ast::SelfParam) -> Option<Ty> {
        let keyword = s
            .self_token()
            .map_or_else(|| self.at(s.syntax()), |t| self.at_token(&t));
        let written = s.ty();
        // A receiver's type written where none may be is the mistake, which the fix deletes,
        // so the names in it are not resolved.
        if ctx.constructor == 0 {
            let t = written?;
            let at = self.at(t.syntax());
            let typed = TextRange::new(keyword.end(), at.end());
            let message = "a receiver's type is `Self`, which isn't written; only a constructor \
                           trait's methods write theirs, as `self: Self<A>`";
            let fix = Fix::new("delete the receiver's type", vec![Edit::delete(typed)]);
            self.diagnostics
                .push(Diagnostic::new(codes::E0338, keyword, message).with_fix(fix));
            return None;
        }
        let Some(t) = written else {
            let message = format!(
                "a constructor trait's `Self` isn't a type, so this method writes its \
                 receiver's type, as `self: {}`",
                receiver_example(ctx)
            );
            self.error(codes::E0338, keyword, message);
            return None;
        };
        let at = self.at(t.syntax());
        let ty = self.ty(ctx, Some(t));
        let in_trait = matches!(ctx.self_kind, SelfKind::Trait(_));
        let applied = matches!(&ty, Ty::App(head, _) if **head == Ty::SelfTy);
        if in_trait && !applied && ty != Ty::Error {
            let message = format!(
                "a receiver's type is `Self` applied to types, as `{}`",
                receiver_example(ctx)
            );
            self.error(codes::E0338, at, message);
            return None;
        }
        Some(ty)
    }
}

/// How a receiver's type is written where `ctx` is: `Self<A>` in a trait of one argument, and
/// the constructor applied in its impls.
fn receiver_example(ctx: &Ctx) -> String {
    let args: Vec<String> = (0..ctx.constructor)
        .map(|i| char::from(b'A' + u8::try_from(i % 26).unwrap_or(0)).to_string())
        .collect();
    let head = match &ctx.self_kind {
        SelfKind::Impl(Ty::Con(item, _)) => item.name.to_string(),
        _ => "Self".to_owned(),
    };
    format!("{head}<{}>", args.join(", "))
}
