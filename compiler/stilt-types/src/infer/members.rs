//! Members of types and traits: the methods found for a receiver, and members named as
//! `Type.m` or `Trait.m`.

use stilt_diag::{Diagnostic, Edit, Fix, MAX_FIXES, codes};
use stilt_hir::decls::{MemberInfo, MemberKindInfo, TraitMethod, TypeDefInfo};
use stilt_hir::hir::{Arg, Ident, Item, MemberOwner, Name, TypeRef};
use stilt_syntax::{TextRange, TextSize};

use super::types::{Instance, Sig};
use super::{Cx, State, error_node, node};
use crate::implements::Traits;
use crate::tast::{self, Callee, ExprKind};
use crate::ty::{Subst, Ty};

/// The method that a name finds for a receiver.
pub(super) enum Found<'d> {
    Inherent(&'d MemberInfo),
    ViaTrait(Item, &'d TraitMethod),
    Ambiguous(Vec<Item>),
    Missing,
}

/// How a call names a method that several traits have, which each fix rewrites to name one.
pub(super) enum Ambiguous<'h> {
    /// The call `r.m(…)`, at `at`, of the receiver at `receiver`.
    Method {
        at: TextRange,
        receiver: TextRange,
        args: &'h [Arg],
    },
    /// `Type.m`, whose type is at the span.
    Member(TextRange),
}

/// The type constructor at the head of a type.
pub(super) fn head(ty: &Ty) -> Option<Item> {
    match ty {
        Ty::Con(item, _) => Some(item.clone()),
        _ => None,
    }
}

impl<'a> State<'a> {
    fn traits(&self) -> Traits<'_> {
        Traits {
            decls: self.env.decls,
            scope: &self.env.bound_args,
            table: &self.table,
        }
    }

    /// The traits that bound a rigid type, or the head of a constructor parameter applied
    /// (traits.constructor-parameters), which a method call on it finds methods of
    /// (traits.method-resolution).
    fn bounded(&self, rigid: &Ty) -> Vec<Item> {
        let rigid = match rigid {
            Ty::App(head, _) => &**head,
            t => t,
        };
        self.env
            .bounds
            .iter()
            .filter(|(v, _)| v == rigid)
            .flat_map(|(_, traits)| traits.iter().cloned())
            .collect()
    }

    fn trait_methods(&self, trait_item: &Item, name: &str) -> Vec<&'a TraitMethod> {
        let decls = self.env.decls;
        decls
            .trait_info(trait_item)
            .map(|info| info.methods.iter().filter(|m| &*m.name == name).collect())
            .unwrap_or_default()
    }

    /// The method `name` of a receiver of type `ty` (traits.method-resolution).
    pub(super) fn find_method(&self, ty: &Ty, name: &str) -> Found<'a> {
        let via = |traits: &[Item]| {
            let found: Vec<(Item, &'a TraitMethod)> = traits
                .iter()
                .flat_map(|t| {
                    self.trait_methods(t, name)
                        .into_iter()
                        .map(move |m| (t.clone(), m))
                })
                .collect();
            match found.as_slice() {
                [] => Found::Missing,
                [(t, m)] => Found::ViaTrait(t.clone(), m),
                many => Found::Ambiguous(many.iter().map(|(t, _)| t.clone()).collect()),
            }
        };
        let implemented: Vec<Item> = self
            .env
            .traits
            .iter()
            .filter(|t| self.traits().has_impl(ty, t))
            .cloned()
            .collect();
        let decls = self.env.decls;
        match self.table.shape(ty) {
            Ty::Con(item, _) => decls
                .inherent_members(&item)
                .iter()
                .find(|m| &*m.name == name)
                .map_or_else(|| via(&implemented), Found::Inherent),
            Ty::App(head, _) if self.table.unsolved(&head).is_some() => Found::Missing,
            rigid @ (Ty::Param(_) | Ty::SelfTy | Ty::App(..)) => via(&self.bounded(&rigid)),
            Ty::Tuple(_) | Ty::Fn(_) | Ty::Spread(_) | Ty::Handler(_) => via(&implemented),
            Ty::Var(_) | Ty::Value(_) | Ty::Error => Found::Missing,
        }
    }

    /// Whether a method `name` that `ty` lacks is one that an error leaves out, whose uses have
    /// the error type (errors.error-type): a member of an impl with an error, for the type
    /// constructor of `ty` or for one that its error hides, or a method that a syntax error
    /// leaves without a signature, of an impl or of a trait that `ty` implements or is bounded
    /// by.
    pub(super) fn left_out(&self, ty: &Ty, name: &str) -> bool {
        let owner = head(ty);
        // A program's impls add no member to the library's types, so the library's own code
        // never meets one that an error leaves out, whatever type a broken impl names.
        let broken = !self.env.std
            && self
                .env
                .decls
                .broken()
                .iter()
                .any(|(o, n)| &**n == name && (o.is_none() || *o == owner));
        broken || {
            let traits: Vec<Item> = match self.table.shape(ty) {
                rigid @ (Ty::Param(_) | Ty::SelfTy | Ty::App(..)) => self.bounded(&rigid),
                _ => self
                    .env
                    .traits
                    .iter()
                    .filter(|t| self.traits().has_impl(ty, t))
                    .cloned()
                    .collect(),
            };
            traits.iter().any(|t| self.unknown_in(t, name))
        }
    }

    /// Whether a trait has a method `name` that a syntax error leaves without a signature.
    fn unknown_in(&self, trait_item: &Item, name: &str) -> bool {
        self.env
            .decls
            .trait_info(trait_item)
            .is_some_and(|info| info.unknown_methods.iter().any(|n| &**n == name))
    }

    /// program.visibility.
    pub(super) fn require_visible(&mut self, name: &Ident, m: &MemberInfo) {
        if !(m.is_pub || m.owner.home == self.env.module) {
            let message = format!("`{}` is private to module `{}`", name.name, m.owner.home);
            self.error(codes::E0213, name.at, message);
        }
    }

    /// traits.ambiguous-methods, with a fix for each of the first two traits, which names it.
    pub(super) fn ambiguous(&mut self, name: &Ident, traits: &[Item], call: &Ambiguous<'_>) {
        let listed: Vec<String> = traits.iter().map(|t| format!("`{}`", t.name)).collect();
        let message = format!("`{}` is a method of {}", name.name, listed.join(" and "));
        let fixes = traits
            .iter()
            .take(MAX_FIXES)
            .filter_map(|t| {
                let tr = self.spelled(t)?;
                let m = &name.name;
                let edits = match call {
                    Ambiguous::Method { at, receiver, args } => {
                        let rest = args.first().map_or(at.end(), |a| a.at.start());
                        let close = if args.is_empty() { ")" } else { ", " };
                        vec![
                            Edit::replace(
                                TextRange::new(at.start(), receiver.start()),
                                format!("{tr}.{m}("),
                            ),
                            Edit::replace(TextRange::new(receiver.end(), rest), close),
                        ]
                    }
                    Ambiguous::Member(ty) => vec![Edit::replace(*ty, tr.clone())],
                };
                Some(Fix::new(format!("call `{tr}`'s `{m}`"), edits))
            })
            .collect();
        self.error_fixed(codes::E0319, name.at, message, fixes);
    }

    /// The names of the methods of a receiver of type `ty`, or of all its members unless
    /// `methods_only`, among which a failed lookup finds the closest (goal closest-candidates).
    pub(super) fn method_names(&self, ty: &Ty, methods_only: bool) -> Vec<Name> {
        let decls = self.env.decls;
        let resolved = self.table.shape(ty);
        let traits: Vec<Item> = match &resolved {
            Ty::Param(_) | Ty::SelfTy | Ty::App(..) => self.bounded(&resolved),
            Ty::Var(_) | Ty::Error => Vec::new(),
            _ => self
                .env
                .traits
                .iter()
                .filter(|t| self.traits().has_impl(&resolved, t))
                .cloned()
                .collect(),
        };
        let mut names: Vec<Name> = match &resolved {
            Ty::Con(item, _) => decls
                .inherent_members(item)
                .iter()
                .filter(|m| m.is_pub || m.owner.home == self.env.module)
                .filter(|m| !methods_only || matches!(m.kind, MemberKindInfo::Method(_)))
                .map(|m| m.name)
                .collect(),
            _ => Vec::new(),
        };
        for t in &traits {
            names.extend(self.trait_method_names(t));
        }
        names
    }

    fn trait_method_names(&self, trait_item: &Item) -> Vec<Name> {
        let decls = self.env.decls;
        decls
            .trait_info(trait_item)
            .map(|info| info.methods.iter().map(|m| m.name).collect())
            .unwrap_or_default()
    }

    /// A method of a trait, named as `Trait.m`. A function without `self` or a constant named that
    /// way is E0330: nothing names the type whose impl is meant (traits.functions-without-self).
    fn trait_member(
        &mut self,
        at: TextRange,
        trait_item: &Item,
        name: &Ident,
        expected: Option<&Ty>,
    ) -> Option<(Callee, Instance)> {
        let Some(m) = self.trait_methods(trait_item, &name.name).first().copied() else {
            if !self.unknown_in(trait_item, &name.name) {
                let message = format!("`{}` has no method `{}`", trait_item.name, name.name);
                let methods = self.trait_method_names(trait_item);
                self.not_found(codes::E0314, name, message, methods.iter().map(|n| &**n));
            }
            return None;
        };
        if !m.is_method() {
            self.named_without_type(at, trait_item, (name, m), expected);
            return None;
        }
        let receiver = self.fresh(at);
        let self_ty = self.self_for(trait_item, &receiver, at);
        self.obligation(
            self.implementer(trait_item, &receiver, &self_ty),
            trait_item.clone(),
            name.at,
        );
        let fixed = self.trait_params(trait_item, &receiver, at);
        let sig = Sig::of(&m.signature, None).with_fixed(fixed);
        let inst = self.instantiate(name.at, &sig, Some(&self_ty), at);
        Some((
            Callee::TraitMethod(trait_item.clone(), m.name, receiver),
            inst,
        ))
    }

    /// E0330: `Trait.f` for a function without `self`, or `Trait.NAME`, at the path that names
    /// the trait, whose fix writes the type the use expects there instead.
    fn named_without_type(
        &mut self,
        at: TextRange,
        trait_item: &Item,
        (name, m): (&Ident, &TraitMethod),
        expected: Option<&Ty>,
    ) {
        let dot = name
            .at
            .start()
            .checked_sub(TextSize::from(1))
            .unwrap_or(at.start());
        let path = TextRange::new(at.start(), dot.max(at.start()));
        let what = if m.kind == MemberKindInfo::Constant {
            "constant"
        } else {
            "function without `self`"
        };
        let ty = expected
            .map(|t| self.table.shape(t))
            .filter(|t| self.traits().has_impl(t, trait_item) || !self.bounded(t).is_empty())
            .and_then(|t| self.written(&t).map(|w| (w, t)));
        let example = ty.as_ref().map_or("T", |(w, _)| w.as_str());
        let message = format!(
            "`{}` is a {what} of `{}`, so it is named on a type, as `{example}.{}`",
            m.name, trait_item.name, m.name
        );
        let fixes = ty
            .map(|(w, _)| Fix::new(format!("name `{w}`"), vec![Edit::replace(path, w)]))
            .into_iter()
            .collect();
        self.error_fixed(codes::E0330, path, message, fixes);
    }

    /// A member of a type, named as `Type.m`.
    fn type_member(
        &mut self,
        at: TextRange,
        t: &TypeRef,
        name: &Ident,
    ) -> Option<(Callee, Instance)> {
        let ty = self.named_type(t);
        let resolved = self.resolved(&ty);
        if resolved == Ty::Error {
            return None;
        }
        match self.find_method(&resolved, &name.name) {
            Found::Inherent(m) => {
                self.require_visible(name, m);
                let inst = self.instantiate(name.at, &Sig::of(&m.signature, None), None, at);
                let impl_params: Vec<_> = m.impl_generics.iter().map(|(v, _)| v.clone()).collect();
                let impl_args: Vec<Ty> =
                    inst.targs.iter().take(impl_params.len()).cloned().collect();
                let impl_self = self.table.subst(
                    &Subst {
                        types: impl_params.into_iter().zip(impl_args).collect(),
                        ..Subst::default()
                    },
                    &Ty::from_hir(&m.self_ty, None),
                );
                self.expect(t.at, &impl_self, &resolved);
                Some((Callee::Member(m.owner.clone(), m.name), inst))
            }
            Found::ViaTrait(trait_item, m) => {
                if m.kind == MemberKindInfo::Constant {
                    self.leave_undecided(&resolved);
                }
                self.obligation(&resolved, trait_item.clone(), name.at);
                let self_ty = self.self_for(&trait_item, &resolved, at);
                let fixed = self.trait_params(&trait_item, &resolved, at);
                let sig = Sig::of(&m.signature, None).with_fixed(fixed);
                let inst = self.instantiate(name.at, &sig, Some(&self_ty), at);
                Some((Callee::TraitMethod(trait_item, m.name, resolved), inst))
            }
            Found::Ambiguous(traits) => {
                self.ambiguous(name, &traits, &Ambiguous::Member(t.at));
                None
            }
            Found::Missing => {
                if self.variant_through_type(&resolved, name, t.at) {
                    return None;
                }
                if !self.left_out(&resolved, &name.name) {
                    let message =
                        format!("`{}` has no member `{}`", self.show(&resolved), name.name);
                    let members = self.method_names(&resolved, false);
                    self.not_found(codes::E0314, name, message, members.iter().map(|n| &**n));
                }
                None
            }
        }
    }

    /// A member of a type or a trait, named as `Type.m` or `Trait.m` (traits.qualified-calls and
    /// traits.associated-functions), as a callee with its instantiated signature. `expected` is the
    /// type the use expects, if it is known, which a fix of E0330 writes.
    pub(super) fn member(
        &mut self,
        at: TextRange,
        owner: &MemberOwner,
        name: &Ident,
        expected: Option<&Ty>,
    ) -> Option<(Callee, Instance)> {
        match owner {
            MemberOwner::Trait(t) => self.trait_member(at, t, name, expected),
            MemberOwner::Type(t) => self.type_member(at, t, name),
        }
    }

    /// traits.trait-constants: a trait's constant has one value for each impl, so naming it on a
    /// type written without its arguments, as `List.MAX`, leaves them undecided, which is no error.
    fn leave_undecided(&mut self, ty: &Ty) {
        let Ty::Con(_, args) = ty else { return };
        for a in args {
            if let Some(v) = self.table.unsolved(a) {
                self.unknown.push(v.id);
            }
        }
    }

    /// Whether a callee is a trait's constant, which a use reads rather than calls
    /// (traits.trait-constants).
    pub(super) fn is_trait_constant(&self, callee: &Callee) -> bool {
        let Callee::TraitMethod(t, n, _) = callee else {
            return false;
        };
        self.trait_methods(t, n)
            .first()
            .is_some_and(|m| m.kind == MemberKindInfo::Constant)
    }

    /// projections.call-is-place: a projection's call is a place, so its name is only called, and
    /// E0426 anywhere else.
    pub(super) fn projection_value(&mut self, at: TextRange) -> tast::Expr {
        let message = "a projection can only be called: its call is a place, so it has no \
                       function type";
        self.error(codes::E0426, at, message.to_owned());
        error_node(at)
    }

    pub(super) fn member_value(
        &mut self,
        cx: &mut Cx,
        (at, expected): (TextRange, Option<&Ty>),
        owner: &MemberOwner,
        name: &Ident,
    ) -> tast::Expr {
        if let Some(value) = self.reflect_value(at, owner, name) {
            return value;
        }
        let Some((target, inst)) = self.member(at, owner, name, expected) else {
            return error_node(at);
        };
        if inst.projection {
            return self.projection_value(at);
        }
        // traits.trait-constants: a trait's constant is read through the impl of the type it is
        // named on, as a call of it with no arguments.
        if self.is_trait_constant(&target) {
            self.perform_call(cx, inst.row.clone(), at);
            let kind = ExprKind::Call(target, inst.targs, Vec::new(), inst.row);
            return node(kind, inst.ret, at);
        }
        if let (Callee::Member(item, n), MemberOwner::Type(_)) = (&target, owner) {
            let is_constant = self
                .env
                .decls
                .inherent_members(item)
                .iter()
                .find(|m| m.name == *n)
                .is_some_and(|m| m.kind == MemberKindInfo::Constant);
            if is_constant {
                // declarations.impl-constants: the constant is the same for every type argument, so
                // `Type.NAME` leaves them undecided.
                for t in &inst.targs {
                    if let Some(v) = self.table.unsolved(t) {
                        self.unknown.push(v.id);
                    }
                }
                let kind = ExprKind::MemberConstant(item.clone(), *n, inst.targs);
                return node(kind, inst.ret, at);
            }
        }
        let ty = Ty::func(inst.params, inst.ret, inst.row);
        self.c_use(&target, &inst.targs, at);
        node(ExprKind::Callee(target, inst.targs), ty, at)
    }
}

impl State<'_> {
    /// `Shape.Circle`, a variant named through its type, as other languages write it: E0314 says
    /// that a variant is named alone (declarations.variant-types), and the fix deletes the type.
    fn variant_through_type(&mut self, ty: &Ty, name: &Ident, type_at: TextRange) -> bool {
        let Ty::Con(item, _) = ty else { return false };
        let Some(TypeDefInfo::Variants(variants)) = self.env.decls.type_info(item).map(|t| &t.def)
        else {
            return false;
        };
        if !variants.iter().any(|(n, _)| *n == name.name) {
            return false;
        }
        let message = format!(
            "`{}` is a variant, named alone rather than through `{}`",
            name.name,
            self.show(ty)
        );
        let written = TextRange::new(type_at.start(), name.at.start());
        let fix = Fix::new("name the variant alone", vec![Edit::delete(written)]);
        let d = Diagnostic::new(codes::E0314, name.at, message)
            .with_help("A variant's name is visible wherever its type is, in patterns and in expressions alike.")
            .with_fix(fix);
        self.errors.push(d);
        true
    }
}
