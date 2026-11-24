//! Impl blocks: their type, their trait and their members (program.visibility; traits.impl-blocks).

use stilt_diag::codes;
use stilt_syntax::TextRange;
use stilt_syntax::ast::{self, AstNode};

use super::bounds::GenericsOf;
use super::{Ctx, Meaning, Resolver, SelfKind};
use crate::hir::{DeclId, Ident, Impl, Member, Owner, TraitRef, Ty};
use crate::scope::{Kind, Namespace};

impl Resolver<'_> {
    /// An impl block, with the names of its members. Other modules see the signature of a
    /// `pub` member of an inherent impl of a `pub` type, and so the block's generics when it
    /// has such a member (program.visibility). A trait impl's methods have the trait's signatures.
    /// An impl block, the names of its members, and where its `where` clause's bounds on
    /// fixed member types are written, in the order of [`Impl::fixed`].
    pub(super) fn impl_block(
        &mut self,
        i: &ast::Impl,
        id: &DeclId,
    ) -> (Impl, Vec<Ident>, Vec<TextRange>) {
        let trait_ty = i.trait_ty();
        let public_type = trait_ty.is_none() && self.is_public_type(i.self_ty());
        let members: Vec<_> = i.members().collect();
        let mut ctx = Ctx {
            public: public_type && members.iter().any(is_pub),
            ..Ctx::module()
        };
        let owner = Owner {
            decl: id.clone(),
            member: None,
        };
        let generics = self.generics(
            &mut ctx,
            (i.generic_list(), i.where_clause()),
            &owner,
            GenericsOf::Impl,
        );
        let (fixed, wheres) = std::mem::take(&mut ctx.fixed)
            .into_iter()
            .map(|(t, item, args, at)| ((t, item, args), at))
            .unzip();
        let trait_ref = trait_ty.map(|t| self.impl_trait(&ctx, &t));
        let arity = match &trait_ref {
            Some(TraitRef::Trait(item, _)) => self.shape_of(item).arity,
            _ => 0,
        };
        let self_ty = if arity > 0 {
            self.constructor_of_impl(&ctx, i.self_ty(), arity)
        } else {
            self.ty(&ctx, i.self_ty())
        };
        let names = self.member_names(&members, trait_ref.is_some());
        let ctx = Ctx {
            self_kind: SelfKind::Impl(self_ty.clone()),
            constructor: arity,
            trait_member: trait_ref.is_some(),
            ..ctx
        };
        let generic = !generics.is_empty();
        let members = (0..)
            .zip(&members)
            .map(|(j, m)| self.impl_member(&ctx, m, generic, public_type, id, j))
            .collect();
        let block = Impl {
            generics,
            trait_ref,
            self_ty,
            members,
            fixed,
        };
        (block, names, wheres)
    }

    /// The trait of a trait impl, with one argument for each of its parameters
    /// (traits.trait-arguments).
    fn impl_trait(&mut self, ctx: &Ctx, t: &ast::Type) -> TraitRef {
        let ast::Type::NamedType(named) = t else {
            return self.trait_ref(ctx, &[]);
        };
        let path = self.path(named.path());
        let args: Vec<ast::Type> = named.args().collect();
        let TraitRef::Trait(item, _) = self.trait_ref(ctx, &path) else {
            for a in args {
                self.ty(ctx, Some(a));
            }
            return TraitRef::Error;
        };
        let shape = self.shape_of(&item);
        if args.len() != shape.params.len() {
            // The impl is still the trait's, each argument the error type, so its members are
            // checked against the trait's (errors.declarations-with-errors, "Declarations with
            // errors").
            self.wrong_trait_args(self.at(named.syntax()), &item, &shape, args.len());
            for a in args {
                self.ty(ctx, Some(a));
            }
            return TraitRef::Trait(item, vec![Ty::Error; shape.params.len()]);
        }
        let args = args.into_iter().map(|a| self.ty(ctx, Some(a))).collect();
        TraitRef::Trait(item, args)
    }

    /// The type of an impl of a constructor trait of arity `arity`: a type constructor of that
    /// arity, written without its arguments (traits.constructor-impls).
    fn constructor_of_impl(&mut self, ctx: &Ctx, t: Option<ast::Type>, arity: u32) -> Ty {
        let Some(t) = t else { return Ty::Error };
        let at = self.at(t.syntax());
        let wrong = |this: &mut Self, what: String| {
            let plural = if arity == 1 { "" } else { "s" };
            let message = format!(
                "{what}, but this trait is over type constructors of {arity} argument{plural}, \
                 named without them, as `List`"
            );
            this.error(codes::E0337, at, message);
            Ty::Error
        };
        let named = match &t {
            ast::Type::NamedType(n) if n.args().next().is_none() => n.clone(),
            ast::Type::NamedType(_) => {
                self.ty(ctx, Some(t.clone()));
                return wrong(self, "this is a type applied to its arguments".to_owned());
            }
            _ => {
                self.ty(ctx, Some(t.clone()));
                return wrong(self, "this is no type constructor".to_owned());
            }
        };
        let path = self.path(named.path());
        match self.walk_to_end(ctx, Namespace::Types, "a type", &path) {
            (Meaning::Broken, _) => Ty::Error,
            (Meaning::Item(item, entry), _) if entry.kind == Kind::Type && entry.arity == arity => {
                Ty::Con(item, Vec::new())
            }
            (Meaning::Item(item, entry), _) if entry.kind == Kind::Type => {
                let n = entry.arity;
                let what = format!(
                    "`{}` takes {n} type argument{}",
                    item.name,
                    if n == 1 { "" } else { "s" }
                );
                wrong(self, what)
            }
            (m, last) => {
                self.wrong_kind(&path[last], &m, "a type");
                Ty::Error
            }
        }
    }

    /// Whether an impl's type is one of the module's `pub` types. The type of an inherent impl
    /// is one of its module's own types (traits.inherent-names), named by a single name.
    fn is_public_type(&self, ty: Option<ast::Type>) -> bool {
        let Some(ast::Type::NamedType(named)) = ty else {
            return false;
        };
        let path = self.path(named.path());
        let types = &self.own.types;
        path.len() == 1 && types.get(&path[0].name).is_some_and(|e| e.is_pub)
    }

    /// The names of an impl block's members, which a trait impl declares at most once each.
    fn member_names(&mut self, members: &[ast::Item], in_trait_impl: bool) -> Vec<Ident> {
        let names: Vec<_> = members.iter().map(|m| self.member_name(m)).collect();
        for n in &names {
            self.check_not_primitive(n);
        }
        if in_trait_impl {
            self.check_unique("a member of this impl", &names);
        }
        names
    }

    /// The member at place `j` of a block, which is `generic` when the block has generics.
    fn impl_member(
        &mut self,
        ctx: &Ctx,
        m: &ast::Item,
        generic: bool,
        public_type: bool,
        id: &DeclId,
        j: u32,
    ) -> Member {
        // declarations.impl-constants: a constant is the same for every type argument, so its type
        // names neither the block's type parameters nor `Self`; a trait's constant has a value for
        // each impl, whose type may name both (traits.trait-constants).
        let ctx = match m {
            ast::Item::Const(_) if generic && !ctx.trait_member => Ctx {
                type_params: Vec::new(),
                self_kind: SelfKind::None,
                ..ctx.clone()
            },
            _ => ctx.clone(),
        };
        let owner = Owner {
            decl: id.clone(),
            member: Some(j),
        };
        self.member(&ctx, m, public_type && is_pub(m), &owner)
    }
}

/// Whether a member of an impl block is written `pub`.
fn is_pub(member: &ast::Item) -> bool {
    match member {
        ast::Item::Fn(f) => f.is_pub(),
        ast::Item::Const(c) => c.is_pub(),
        _ => false,
    }
}
