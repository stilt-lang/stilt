//! Impl blocks: their types, their members, and the rules they follow (traits.impl-blocks and
//! traits.implementing-trait and traits.method-resolution, traits.traits-in-scope,
//! traits.ambiguous-methods and traits.name-clashes).

use std::collections::BTreeSet;
use stilt_diag::codes;

use super::build::{Builder, Unit};
use super::implements::structural_traits;
use super::signatures::{
    bound_args_of, bounds_of, const_signature, matches_trait, signature, values_of,
};
use super::{BoundArgs, Bounds, ImplInfo, MemberInfo, MemberKindInfo, TraitInfo};
use crate::Anchor;
use crate::hir::{DeclId, GenericId, Impl, Item, ItemHir, MemberKind, Name, Param, TraitRef, Ty};

/// An impl block, with its module and what its type names.
struct Site<'a> {
    pub(super) unit: &'a Unit<'a>,
    pub(super) index: u32,
    pub(super) block: &'a Impl,
    pub(super) generics: Bounds,
    /// The value parameters among its generics, with their types (generics.value-parameters).
    pub(super) values: Vec<(GenericId, Ty)>,
    /// The arguments its generics' bounds give traits with parameters (traits.bound-arguments).
    pub(super) bound_args: Vec<BoundArgs>,
    pub(super) head: Head,
}

enum Head {
    /// A valid type: this constructor, applied.
    Valid(Item),
    /// A type with an error, and its constructor if the error leaves it known.
    Broken(Option<Item>),
}

impl Builder {
    /// Adds every impl block, in the order of the program (errors.several-places): the inherent
    /// ones first, so that each trait impl sees every inherent method of its type.
    pub(super) fn add_impls(&mut self, units: &[Unit<'_>]) {
        let sites = self.sites(units);
        let mut methods = Vec::new();
        for site in &sites {
            match (&site.head, &site.block.trait_ref) {
                (Head::Broken(owner), _) => self.add_broken(site, owner.as_ref()),
                (Head::Valid(owner), Some(TraitRef::Error)) => self.add_broken(site, Some(owner)),
                (Head::Valid(owner), None) => {
                    for (member, j) in self.add_inherent(site, owner) {
                        methods.push((site.unit, Anchor::Member(site.index, j), member));
                    }
                }
                (Head::Valid(_), Some(TraitRef::Trait(..))) => {}
            }
        }
        for site in &sites {
            if let (Head::Valid(owner), Some(TraitRef::Trait(trait_item, args))) =
                (&site.head, &site.block.trait_ref)
            {
                self.add_trait_impl(site, owner, (trait_item, args));
            }
        }
        self.check_structural_clashes(&methods);
    }

    /// Every impl block, in the order of the program, with what its type names.
    fn sites<'a>(&mut self, units: &'a [Unit<'a>]) -> Vec<Site<'a>> {
        let mut blocks: Vec<(&Unit<'_>, u32, &Impl)> = units
            .iter()
            .flat_map(|unit| {
                (0..)
                    .zip(&unit.hir.items)
                    .filter_map(move |(index, item)| match item {
                        ItemHir::Impl(block) => Some((unit, index, block)),
                        _ => None,
                    })
            })
            .collect();
        blocks.sort_by(|(a, i, _), (b, j, _)| (a.path, i).cmp(&(b.path, j)));
        blocks
            .into_iter()
            .map(|(unit, index, block)| {
                let owner = unit.owner(index, None);
                let generics = bounds_of(&block.generics, &owner);
                let bound_args = bound_args_of(&block.generics, &owner);
                let head = self.head(unit, index, block, &generics);
                Site {
                    unit,
                    index,
                    block,
                    generics,
                    values: values_of(&block.generics, &owner),
                    bound_args,
                    head,
                }
            })
            .collect()
    }

    /// traits.impl-blocks and traits.implementing-trait: an impl's type is a type constructor
    /// applied to the impl's type parameters, each once, but for its member types, which its bounds
    /// give (traits.member-types).
    fn head(&mut self, unit: &Unit<'_>, index: u32, block: &Impl, generics: &Bounds) -> Head {
        let invalid = |this: &mut Self, owner| {
            let message = "an impl's type must be a type applied to the impl's own type \
                           parameters, each once"
                .to_owned();
            this.problem(unit, Anchor::ImplType(index), codes::E0302, message);
            Head::Broken(owner)
        };
        match &block.self_ty {
            Ty::Error => Head::Broken(None),
            Ty::Con(item, args) if args.contains(&Ty::Error) => Head::Broken(Some(item.clone())),
            Ty::Con(item, args) => {
                let params: Vec<_> = args
                    .iter()
                    .filter_map(|a| match a {
                        Ty::Param(v) => Some(v),
                        _ => None,
                    })
                    .collect();
                let unique: BTreeSet<_> = params.iter().copied().collect();
                let mut ids: Vec<_> = generics
                    .iter()
                    .map(|(v, _)| v)
                    .filter(|v| {
                        !block
                            .generics
                            .get(v.index as usize)
                            .is_some_and(|g| g.member)
                    })
                    .collect();
                ids.sort();
                if params.len() == args.len()
                    && params.len() == ids.len()
                    && unique.into_iter().collect::<Vec<_>>() == ids
                {
                    Head::Valid(item.clone())
                } else {
                    invalid(self, Some(item.clone()))
                }
            }
            Ty::Param(_)
            | Ty::SelfTy
            | Ty::App(..)
            | Ty::Tuple(_)
            | Ty::Fn(_)
            | Ty::Handler(_)
            | Ty::Value(_)
            | Ty::Spread(..) => invalid(self, None),
        }
    }

    /// The members of an impl for the type constructor `owner`, each with its place. Those that a
    /// syntax error leaves without a signature are none, and every use of them has the error
    /// type (errors.invalid-source-text and errors.error-type).
    fn members(&mut self, site: &Site<'_>, owner: &Item, is_trait: bool) -> Vec<(MemberInfo, u32)> {
        for member in site.block.members.iter().filter(|m| m.unknown) {
            self.decls
                .broken
                .push((Some(owner.clone()), *member.name()));
        }
        let type_pub = self.decls.types.get(owner).is_some_and(|info| info.is_pub);
        (0..)
            .zip(&site.block.members)
            .filter(|(_, member)| !member.unknown)
            .map(|(j, member)| {
                let (kind, signature) = match &member.kind {
                    MemberKind::Fn(f) => {
                        let kind = match f.params.first() {
                            Some(Param::SelfParam(mode, _)) => MemberKindInfo::Method(*mode),
                            _ => MemberKindInfo::Function,
                        };
                        let owner = site.unit.owner(site.index, Some(j));
                        let outer = (&site.generics, site.bound_args.as_slice());
                        let mut s = signature(f, &owner, &site.block.self_ty, outer);
                        s.values.splice(0..0, site.values.iter().cloned());
                        (kind, s)
                    }
                    MemberKind::Const(c) => {
                        let owner = site.unit.owner(site.index, Some(j));
                        let mut s = const_signature(&owner, &site.generics, &c.ty);
                        s.values.clone_from(&site.values);
                        (MemberKindInfo::Constant, s)
                    }
                    MemberKind::TraitConst(_, ty, _) => {
                        let owner = site.unit.owner(site.index, Some(j));
                        let mut s = const_signature(&owner, &site.generics, ty);
                        s.values.clone_from(&site.values);
                        (MemberKindInfo::Constant, s)
                    }
                };
                let info = MemberInfo {
                    name: *member.name(),
                    is_pub: is_trait || (member.is_pub && type_pub),
                    kind,
                    signature,
                    owner: owner.clone(),
                    impl_generics: site.generics.clone(),
                    self_ty: site.block.self_ty.clone(),
                };
                (info, j)
            })
            .collect()
    }

    /// Records the members of an impl with an error, whose uses have the error type
    /// (errors.broken-blocks and errors.error-type).
    fn add_broken(&mut self, site: &Site<'_>, owner: Option<&Item>) {
        for member in &site.block.members {
            self.decls.broken.push((owner.cloned(), *member.name()));
        }
    }

    /// Adds an inherent impl, and returns its members with their places. An impl outside the
    /// type's home module adds no member, so it changes no other module (traits.impl-blocks).
    fn add_inherent(&mut self, site: &Site<'_>, owner: &Item) -> Vec<(MemberInfo, u32)> {
        if owner.home != site.unit.hir.name {
            let message = format!(
                "only the home module of `{}`, `{}`, may hold its impl blocks",
                owner.name, owner.home
            );
            self.problem(
                site.unit,
                Anchor::ImplType(site.index),
                codes::E0301,
                message,
            );
            self.add_broken(site, Some(owner));
            return Vec::new();
        }
        let members = self.members(site, owner, false);
        self.decls
            .inherent
            .entry(owner.clone())
            .or_default()
            .extend(members.iter().map(|(m, _)| m.clone()));
        members
    }

    /// traits.implementing-trait, and traits.impl-members: an impl holds each function and constant
    /// of the trait without a default, and no other member, each with the signature the trait
    /// declares, its parameters replaced by the impl's arguments.
    fn check_trait_methods(
        &mut self,
        site: &Site<'_>,
        (trait_item, trait_args): (&Item, &[Ty]),
        owner: &Item,
        members: &[(MemberInfo, u32)],
    ) {
        let Some(info) = self.decls.traits.get(trait_item).cloned() else {
            return;
        };
        let unknown = |name: &Name| {
            site.block
                .members
                .iter()
                .any(|m| m.unknown && m.name() == name)
        };
        for method in &info.methods {
            if !method.has_default
                && !members.iter().any(|(m, _)| m.name == method.name)
                && !unknown(&method.name)
            {
                let what = describe(method.kind);
                let message = format!(
                    "the impl of `{}` for `{}` lacks the {what} `{}`",
                    trait_item.name, owner.name, method.name
                );
                self.problem(site.unit, Anchor::Item(site.index), codes::E0305, message);
            }
        }
        let params: Vec<(GenericId, Ty)> = info
            .params
            .iter()
            .cloned()
            .zip(trait_args.iter().cloned())
            .collect();
        for (member, j) in members {
            self.check_trait_member(site, (trait_item, &info, &params), member, *j);
        }
    }

    /// traits.impl-signatures: one member of a trait impl is a member of the trait, of its kind and
    /// with its signature.
    fn check_trait_member(
        &mut self,
        site: &Site<'_>,
        (trait_item, info, params): (&Item, &TraitInfo, &[(GenericId, Ty)]),
        member: &MemberInfo,
        j: u32,
    ) {
        let at = Anchor::Member(site.index, j);
        let Some(method) = info.methods.iter().find(|m| m.name == member.name) else {
            if !info.unknown_methods.contains(&member.name) {
                let message = format!("`{}` is not a member of `{}`", member.name, trait_item.name);
                self.problem(site.unit, at, codes::E0306, message);
            }
            return;
        };
        let constant = |k| k == MemberKindInfo::Constant;
        if constant(method.kind) != constant(member.kind) {
            let message = format!(
                "`{}` is a {} of `{}`, so the impl declares it as one",
                member.name,
                describe(method.kind),
                trait_item.name
            );
            self.problem(site.unit, at, codes::E0307, message);
            return;
        }
        let own = site.generics.len();
        let self_ty = (&site.block.self_ty, params);
        if !matches_trait(self_ty, &method.signature, &member.signature, own) {
            let message = format!(
                "`{}` must have the signature that `{}` declares",
                member.name, trait_item.name
            );
            self.problem(site.unit, at, codes::E0307, message);
        }
    }

    /// Adds a trait impl, after every inherent impl, with the arguments it gives the trait's
    /// parameters (traits.trait-arguments).
    fn add_trait_impl(
        &mut self,
        site: &Site<'_>,
        owner: &Item,
        (trait_item, args): (&Item, &[Ty]),
    ) {
        let module = &site.unit.hir.name;
        // traits.orphan-rule. An orphan impl adds nothing, so it changes no other module.
        if trait_item.home != *module && owner.home != *module {
            let message = format!(
                "an impl of `{}` for `{}` must be in module `{}` or `{}`",
                trait_item.name, owner.name, trait_item.home, owner.home
            );
            self.problem(site.unit, Anchor::Item(site.index), codes::E0303, message);
            self.add_broken(site, Some(owner));
            return;
        }
        // The arguments are fixed by the impl's type, so a second impl for it overlaps
        // whatever its arguments (traits.trait-arguments).
        if self.decls.trait_impl(trait_item, owner).is_some() {
            let message = format!(
                "`{}` already has an impl of `{}`",
                owner.name, trait_item.name
            );
            self.problem(site.unit, Anchor::Item(site.index), codes::E0304, message);
            return;
        }
        let members = self.members(site, owner, true);
        let info = ImplInfo {
            module: *module,
            generics: site.generics.clone(),
            values: site.values.clone(),
            bound_args: site.bound_args.clone(),
            trait_args: args.to_vec(),
            self_ty: site.block.self_ty.clone(),
            decl: DeclId {
                module: *module,
                index: site.index,
            },
            members: members.iter().map(|(m, _)| m.clone()).collect(),
        };
        self.check_trait_methods(site, (trait_item, args), owner, &members);
        self.check_hidden(site, owner, trait_item);
        self.decls
            .trait_impls
            .insert((trait_item.clone(), owner.clone()), info);
    }

    /// traits.name-clashes: a type's inherent members don't share a name with the functions and
    /// constants of the traits it implements (traits.shared-member-names).
    fn check_hidden(&mut self, site: &Site<'_>, owner: &Item, trait_item: &Item) {
        let hidden: Vec<_> = self
            .decls
            .inherent_members(owner)
            .iter()
            .filter(|m| {
                self.decls
                    .methods_of(trait_item)
                    .iter()
                    .any(|t| t.name == m.name)
            })
            .map(|m| (m.name, m.kind))
            .collect();
        for (name, kind) in hidden {
            let message = format!(
                "`{}` has an inherent {} `{name}`, which this impl of `{}` would hide; rename one",
                owner.name,
                describe(kind),
                trait_item.name
            );
            self.problem(site.unit, Anchor::Item(site.index), codes::E0308, message);
        }
    }
    /// traits.name-clashes: an inherent method doesn't share a name with a method of a structural
    /// impl its type has, at the inherent method.
    fn check_structural_clashes(&mut self, methods: &[(&Unit<'_>, Anchor, MemberInfo)]) {
        for (unit, at, member) in methods {
            for trait_item in structural_traits() {
                if self
                    .decls
                    .methods_of(&trait_item)
                    .iter()
                    .any(|m| m.name == member.name)
                    && self.decls.trait_impl(&trait_item, &member.owner).is_none()
                    && self.decls.structural_impl(&member.owner, &trait_item)
                {
                    let message = format!(
                        "`{}` implements `{}`, whose method `{}` this method would hide",
                        member.owner.name, trait_item.name, member.name
                    );
                    self.problem(unit, *at, codes::E0308, message);
                }
            }
        }
    }
}

/// A member of a trait, as messages name its kind.
fn describe(kind: MemberKindInfo) -> &'static str {
    match kind {
        MemberKindInfo::Method(_) => "method",
        MemberKindInfo::Function => "function",
        MemberKindInfo::Constant => "constant",
    }
}
