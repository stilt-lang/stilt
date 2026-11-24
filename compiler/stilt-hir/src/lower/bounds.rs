//! Generics and their bounds (traits.bounds and traits.bounded-blocks), with the arguments of
//! traits that have parameters, the member types that a bound without them gives, and constructor
//! parameters (traits.bound-arguments, traits.member-types and traits.constructor-parameters).

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::ast::{self, AstNode};
use stilt_syntax::{SyntaxKind, TextRange, TextSize};

use super::{Ctx, MemberType, Resolver};
use crate::hir::{Generic, GenericId, GenericKind, Ident, Item, Name, Owner, TraitRef, Ty};
use crate::items::TraitShape;
use crate::scope::is_primitive;

/// Where a list of generics is declared, which decides what its bounds may be.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum GenericsOf {
    Function,
    /// An impl block's, which a constructor trait can't bound (traits.constructor-parameters).
    Impl,
}

/// The generics being declared: those written, then the member types that their bounds give.
pub(super) struct Declared<'o> {
    owner: &'o Owner,
    pub(super) generics: Vec<Generic>,
    /// Where the written generics end, before their `>`.
    end: Option<TextSize>,
}

impl Declared<'_> {
    pub(super) fn id(&self, index: usize) -> GenericId {
        GenericId {
            owner: self.owner.clone(),
            index: u32::try_from(index).expect("under 4G generics"),
        }
    }

    /// The place among these generics of the generic `id`, if it is one of them.
    pub(super) fn index_of(&self, id: &GenericId) -> Option<usize> {
        let index = id.index as usize;
        (id.owner == *self.owner && index < self.generics.len()).then_some(index)
    }
}

impl Resolver<'_> {
    /// The shape of a trait, from its declaration's syntax (traits.trait-parameters and
    /// traits.constructor-traits).
    pub(super) fn shape_of(&self, item: &Item) -> TraitShape {
        self.named_in(&item.home, &item.name)
            .and_then(|named| named.shape.clone())
            .unwrap_or_default()
    }

    /// The generics of a declaration: each name is declared first, so that a bound's argument
    /// may name a later generic (traits.bound-arguments), then each bound is resolved. A trait with
    /// parameters named without its arguments gives each of them a member type, a generic that
    /// follows those written, which the declaration's `where` clause bounds (traits.where).
    pub(super) fn generics(
        &mut self,
        ctx: &mut Ctx,
        (list, clause): (Option<ast::GenericList>, Option<ast::WhereClause>),
        owner: &Owner,
        of: GenericsOf,
    ) -> Vec<Generic> {
        let written: Vec<ast::Generic> = list.iter().flat_map(ast::GenericList::generics).collect();
        let end = list.as_ref().and_then(|l| {
            l.syntax()
                .children_with_tokens()
                .filter_map(rowan::NodeOrToken::into_token)
                .find(|t| t.kind() == SyntaxKind::R_ANGLE)
                .map(|t| self.at_token(&t).start())
        });
        let mut declared = Declared {
            owner,
            generics: Vec::new(),
            end,
        };
        for (index, g) in written.iter().enumerate() {
            let id = declared.id(index);
            let generic = self.declare_generic(ctx, g, id);
            declared.generics.push(generic);
        }
        for (index, g) in written.iter().enumerate() {
            if let ast::Generic::TypeParam(p) = g {
                let id = declared.id(index);
                let bounds = p.bounds().collect::<Vec<_>>();
                let name = declared.generics[index].name;
                let refs = self.bounds(ctx, &mut declared, (&id, &name), &bounds);
                self.check_kinds(ctx, &id, &refs, &bounds, of);
                declared.generics[index].kind = GenericKind::Type(refs);
            }
        }
        self.where_clause(ctx, clause, &mut declared, list.as_ref());
        declared.generics
    }

    /// Declares a written generic, with no bounds yet.
    fn declare_generic(&mut self, ctx: &mut Ctx, g: &ast::Generic, id: GenericId) -> Generic {
        match g {
            ast::Generic::TypeParam(p) => {
                let n = self.name(p.name(), p.syntax());
                self.declare(&mut ctx.type_params, "a type parameter", &n, id.clone());
                if p.is_pack() {
                    ctx.packs.push(id);
                }
                Generic {
                    name: n.name,
                    kind: GenericKind::Type(Vec::new()),
                    member: false,
                    pack: p.is_pack(),
                }
            }
            ast::Generic::RowParam(p) => {
                let n = self.name(p.name(), p.syntax());
                if ["io", "panic", "alloc"].contains(&&*n.name) {
                    let message = format!("a row variable can't be named `{}`", n.name);
                    self.error(codes::E0501, n.at, message);
                } else if is_primitive(&n.name) {
                    let message = format!("`{}` is a primitive type name", n.name);
                    self.error(codes::E0210, n.at, message);
                }
                // A row variable and a value parameter of one list are named apart
                // (generics.value-parameters).
                if ctx.value_params.iter().any(|(name, ..)| *name == n.name) {
                    let message = format!("`{}` is already a value parameter here", n.name);
                    self.error(codes::E0208, n.at, message);
                } else {
                    self.declare(&mut ctx.row_vars, "a row variable", &n, id);
                }
                Generic {
                    name: n.name,
                    kind: GenericKind::Row,
                    member: false,
                    pack: false,
                }
            }
            ast::Generic::ValueParam(p) => {
                let (n, t) = self.value_param(ctx, p, id);
                Generic {
                    name: n.name,
                    kind: GenericKind::Value(t),
                    member: false,
                    pack: false,
                }
            }
        }
    }

    /// The bounds of the type parameter `param`, named `name`, each with its trait's arguments.
    pub(super) fn bounds(
        &mut self,
        ctx: &mut Ctx,
        declared: &mut Declared<'_>,
        (param, name): (&GenericId, &Name),
        bounds: &[ast::Bound],
    ) -> Vec<TraitRef> {
        bounds
            .iter()
            .map(|b| self.bound(ctx, declared, (param, name), b))
            .collect()
    }

    /// One bound (traits.bound-arguments): a trait with all its arguments, or none, each parameter
    /// then a member type of `param` of its own.
    fn bound(
        &mut self,
        ctx: &mut Ctx,
        declared: &mut Declared<'_>,
        (param, name): (&GenericId, &Name),
        b: &ast::Bound,
    ) -> TraitRef {
        if let Some(r) = b.record() {
            return self.record_bound(ctx, &r);
        }
        let Some((item, shape, written)) = self.bound_trait(ctx, b) else {
            return TraitRef::Error;
        };
        let args: Vec<Ty> = if let Some(args) = written {
            args
        } else {
            shape
                .params
                .iter()
                .map(|p| {
                    let id = declared.id(declared.generics.len());
                    declared.generics.push(Generic {
                        name: Name::from(format!("{name}.{p}")),
                        kind: GenericKind::Type(Vec::new()),
                        member: true,
                        pack: false,
                    });
                    Ty::Param(id)
                })
                .collect()
        };
        let unnamed = (!b.has_args() && shape.params.len() == 1)
            .then(|| b.path().map(|p| self.at(p.syntax()).end()))
            .flatten()
            .zip(declared.end);
        for (p, ty) in shape.params.iter().zip(&args) {
            ctx.members.push(MemberType {
                param: param.clone(),
                trait_item: item.clone(),
                name: *p,
                ty: ty.clone(),
                unnamed,
            });
        }
        TraitRef::Trait(item, args)
    }

    /// The trait that the bound `b` names, with its shape and the arguments written for it, if
    /// any. A trait given some but not all of them is E0300, and its arguments are then the error
    /// type (traits.bound-arguments). The arguments of a name that isn't a trait are resolved all
    /// the same, so that a name among them that names nothing is reported (errors.unknown-names).
    fn bound_trait(
        &mut self,
        ctx: &Ctx,
        b: &ast::Bound,
    ) -> Option<(Item, TraitShape, Option<Vec<Ty>>)> {
        let path = self.path(b.path());
        let TraitRef::Trait(item, _) = self.trait_ref(ctx, &path) else {
            for a in b.args() {
                self.ty(ctx, Some(a));
            }
            return None;
        };
        let shape = self.shape_of(&item);
        if !b.has_args() {
            return Some((item, shape, None));
        }
        let given: Vec<ast::Type> = b.args().collect();
        if given.len() != shape.params.len() {
            self.wrong_trait_args(self.at(b.syntax()), &item, &shape, given.len());
        }
        let mut args: Vec<Ty> = given.into_iter().map(|a| self.ty(ctx, Some(a))).collect();
        // The bound stays, its arguments the error type where they are wrong, so its methods are
        // still found.
        if args.len() != shape.params.len() {
            args = vec![Ty::Error; shape.params.len()];
        }
        Some((item, shape, Some(args)))
    }

    /// A bound that bounds no generic of the declaration, as one of a `where` clause on a type
    /// with an error, resolved as any bound is, so that its mistakes are reported: the trait, and
    /// the trait's arguments.
    pub(super) fn loose_bound(&mut self, ctx: &Ctx, b: &ast::Bound) -> TraitRef {
        match self.bound_trait(ctx, b) {
            Some((item, _, args)) => TraitRef::Trait(item, args.unwrap_or_default()),
            None => TraitRef::Error,
        }
    }

    /// E0300: a trait with parameters given the wrong number of arguments (traits.trait-arguments
    /// and traits.bound-arguments).
    pub(super) fn wrong_trait_args(
        &mut self,
        at: TextRange,
        item: &Item,
        shape: &TraitShape,
        given: usize,
    ) {
        let n = shape.params.len();
        let message = if n == 0 {
            format!(
                "`{}` has no parameters, so it takes no type arguments",
                item.name
            )
        } else {
            let all = shape
                .params
                .iter()
                .map(|p| format!("`{p}`"))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "`{}` takes {n} type argument{} ({all}), or none, not {given}",
                item.name,
                if n == 1 { "" } else { "s" }
            )
        };
        self.error(codes::E0300, at, message);
    }

    /// traits.constructor-parameters: a type parameter bounded by a constructor trait is a
    /// constructor parameter of its arity, which no trait over types bounds with it, nor one of
    /// another arity, and which only a function declares.
    fn check_kinds(
        &mut self,
        ctx: &mut Ctx,
        param: &GenericId,
        refs: &[TraitRef],
        bounds: &[ast::Bound],
        of: GenericsOf,
    ) {
        let arities: Vec<(u32, &ast::Bound, &Item)> = refs
            .iter()
            .zip(bounds)
            .filter_map(|(r, b)| match r {
                TraitRef::Trait(item, _) => Some((self.shape_of(item).arity, b, item)),
                TraitRef::Error => None,
            })
            .collect();
        let Some(&(arity, _, constructor)) = arities.iter().find(|(a, ..)| *a > 0) else {
            return;
        };
        if of == GenericsOf::Impl {
            let b = arities.iter().find(|(a, ..)| *a > 0).map(|(_, b, _)| *b);
            let at = b.map_or_else(TextRange::default, |b| self.at(b.syntax()));
            let message = format!(
                "`{}` is a constructor trait, which only a function's generic can name as its \
                 bound",
                constructor.name
            );
            self.error(codes::E0337, at, message);
            return;
        }
        if let Some((other, b, item)) = arities.iter().find(|(a, ..)| *a != arity) {
            let at = self.at(b.syntax());
            let message = if *other == 0 {
                format!(
                    "`{}` is a trait over types, which can't bound a constructor parameter of \
                     `{}`",
                    item.name, constructor.name
                )
            } else {
                format!(
                    "`{}` is over constructors of {other} arguments, and `{}` over \
                     constructors of {arity}",
                    item.name, constructor.name
                )
            };
            self.error(codes::E0337, at, message);
        }
        // The parameter stays one of the first constructor trait's arity, so its uses report
        // nothing more.
        ctx.constructors.push((param.clone(), arity));
    }

    /// E0215 for `Self` outside impl and trait blocks, where it names nothing at all, so that a
    /// member type named on it there is no member type that names nothing (traits.methods).
    fn self_outside_blocks(&mut self, ctx: &Ctx, base: &Ident) -> bool {
        let outside = &*base.name == "Self" && matches!(ctx.self_kind, super::SelfKind::None);
        if outside {
            let message = "`Self` exists only in impl and trait blocks".to_owned();
            self.error(codes::E0215, base.at, message);
        }
        outside
    }

    /// A member type `C.Item` (traits.member-types): `C` is a type parameter, and `Item` a
    /// parameter of the trait of one of its bounds, given by that bound.
    pub(super) fn member_type(&mut self, ctx: &Ctx, path: &[Ident], at: TextRange) -> Ty {
        let (base, member) = (&path[0], &path[1]);
        if self.self_outside_blocks(ctx, base) {
            return Ty::Error;
        }
        let Some((_, param)) = ctx.type_params.iter().rev().find(|(n, _)| *n == base.name) else {
            let message = format!(
                "`{}` isn't a type parameter, so it has no member types; a member type is \
                 named on a type parameter, as `C.{}`",
                base.name, member.name
            );
            self.error(codes::E0334, at, message);
            return Ty::Error;
        };
        let found: Vec<&MemberType> = ctx
            .members
            .iter()
            .filter(|m| m.param == *param && m.name == member.name)
            .collect();
        match found.as_slice() {
            [one] => one.ty.clone(),
            [] => {
                let message = format!(
                    "no bound of `{}` has a parameter `{}`",
                    base.name, member.name
                );
                self.error(codes::E0334, at, message);
                Ty::Error
            }
            [first, second, ..] => {
                let fresh = fresh_name(ctx);
                let named = found.iter().find(|m| m.unnamed.is_some()).unwrap_or(first);
                let message = format!(
                    "`{0}.{1}` could be `{2}`'s `{1}` or `{3}`'s; name it with a generic, as \
                     `{0}: {4}<{fresh}>`",
                    base.name,
                    member.name,
                    first.trait_item.name,
                    second.trait_item.name,
                    named.trait_item.name,
                );
                let mut d = Diagnostic::new(codes::E0335, at, message);
                if let Some((bound_end, list_end)) = named.unnamed {
                    let title = format!(
                        "name `{}`'s `{}` as `{fresh}`",
                        named.trait_item.name, member.name
                    );
                    d = d.with_fix(Fix::new(
                        title,
                        vec![
                            Edit::insert(bound_end, format!("<{fresh}>")),
                            Edit::insert(list_end, format!(", {fresh}")),
                            Edit::replace(at, fresh.clone()),
                        ],
                    ));
                }
                self.diagnostics.push(d);
                Ty::Error
            }
        }
    }
}

/// A name for a new type parameter that names none in scope: `T`, or `T2`, `T3` and on.
pub(super) fn fresh_name(ctx: &Ctx) -> String {
    let taken = |n: &str| ctx.type_params.iter().any(|(m, _)| &**m == n);
    // One of the first names past the parameters in scope is free.
    std::iter::once("T".to_owned())
        .chain((2..=ctx.type_params.len() + 2).map(|i| format!("T{i}")))
        .find(|n| !taken(n))
        .unwrap_or_default()
}
