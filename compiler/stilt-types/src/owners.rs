//! What each body of a module is the code of: a function, with where it is declared, a
//! constant, a test or a doc example.

use stilt_hir::decls::{BoundArgs, Bounds, FnSig, bound_args_of, bounds_of, signature};
use stilt_hir::hir::{
    BodyIndex, DeclId, DeclKind, FnBody, Generic, GenericId, Item, ItemHir, Limits, MemberKind,
    ModuleHir, Name, Owner, TraitRef, Ty,
};

use crate::analyses::implicit::Key;

/// Where a function is declared.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Place {
    Module,
    /// An impl block, of a trait if it has one, for a type constructor if its type is one.
    Impl {
        trait_item: Option<Item>,
        owner: Option<Item>,
    },
    /// A trait, whose default method it is.
    Trait(Item),
}

/// What a body is the code of, all that checking it needs to know of its declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum BodyOwner {
    Fn {
        name: Name,
        signature: Box<FnSig>,
        place: Place,
        /// Whether the body is the function's `= ?`.
        hole: bool,
        /// What the function's own `without` limits (declarations.limits).
        limits: Limits,
        /// Whether it is a procedural macro (macros.procedural-declarations).
        procedural: bool,
    },
    /// A constant, of its type, and the trait whose default it is, if it is one
    /// (traits.trait-constants).
    Const(Ty, Option<Item>),
    Test,
    Example,
}

impl BodyOwner {
    /// The key of the function in the implicit effects of the program, if the body is one's
    /// that the later phases check.
    pub(crate) fn key(&self, module: Name) -> Option<Key> {
        let BodyOwner::Fn { name, place, .. } = self else {
            return None;
        };
        let name = *name;
        match place {
            Place::Module => Some(Key::Function(Item { home: module, name })),
            Place::Impl {
                trait_item: Some(t),
                owner: Some(o),
            } => Some(Key::ImplMethod(t.clone(), o.clone(), name)),
            Place::Impl {
                trait_item: None,
                owner: Some(o),
            } => Some(Key::Member(o.clone(), name)),
            Place::Impl { owner: None, .. } => None,
            Place::Trait(t) => Some(Key::DefaultMethod(t.clone(), name)),
        }
    }
}

fn holds(body: Option<FnBody>, index: BodyIndex) -> Option<bool> {
    match body? {
        FnBody::Block(i) if i == index => Some(false),
        FnBody::Hole(i) if i == index => Some(true),
        FnBody::Block(_) | FnBody::Hole(_) => None,
    }
}

/// What the body `index` of a module is the code of.
pub(crate) fn owner_of(module: &ModuleHir, index: BodyIndex) -> BodyOwner {
    for (i, item) in (0..).zip(&module.items) {
        let decl = DeclId {
            module: module.name,
            index: i,
        };
        let found = match item {
            ItemHir::Use => None,
            ItemHir::Decl(d) => d
                .examples
                .contains(&index)
                .then_some(BodyOwner::Example)
                .or_else(|| in_decl(module, &decl, &d.kind, index)),
            ItemHir::Impl(imp) => {
                let outer = bounds_of(&imp.generics, &owner(&decl, None));
                let outer_args = bound_args_of(&imp.generics, &owner(&decl, None));
                let place = Place::Impl {
                    trait_item: match &imp.trait_ref {
                        Some(TraitRef::Trait(t, _)) => Some(t.clone()),
                        Some(TraitRef::Error) | None => None,
                    },
                    owner: match &imp.self_ty {
                        Ty::Con(item, _) => Some(item.clone()),
                        _ => None,
                    },
                };
                let outer = (&outer, outer_args.as_slice());
                in_members(&imp.members, &decl, index, &imp.self_ty, outer, &place)
            }
        };
        if let Some(found) = found {
            return found;
        }
    }
    unreachable!("every body of a module has an owner")
}

fn owner(decl: &DeclId, member: Option<u32>) -> Owner {
    Owner {
        decl: decl.clone(),
        member,
    }
}

fn in_decl(
    module: &ModuleHir,
    decl: &DeclId,
    kind: &DeclKind,
    index: BodyIndex,
) -> Option<BodyOwner> {
    match kind {
        DeclKind::Fn(f) => holds(f.body, index).map(|hole| BodyOwner::Fn {
            name: f.name,
            signature: Box::new(signature(
                f,
                &owner(decl, None),
                &Ty::Error,
                (&Vec::new(), &[]),
            )),
            place: Place::Module,
            hole,
            limits: f.limits,
            procedural: f.procedural,
        }),
        DeclKind::Const(c) => (c.value == index).then(|| BodyOwner::Const(c.ty.clone(), None)),
        DeclKind::Test(_, body) => (*body == index).then_some(BodyOwner::Test),
        DeclKind::Trait(t) => {
            let trait_item = Item {
                home: module.name,
                name: t.name,
            };
            in_members(
                &t.members,
                decl,
                index,
                &Ty::SelfTy,
                (&Vec::new(), &[]),
                &Place::Trait(trait_item),
            )
        }
        DeclKind::Type(_) | DeclKind::Macro(_) | DeclKind::Effect(_) => None,
    }
}

fn in_members(
    members: &[stilt_hir::hir::Member],
    decl: &DeclId,
    index: BodyIndex,
    self_ty: &Ty,
    outer: (&Bounds, &[BoundArgs]),
    place: &Place,
) -> Option<BodyOwner> {
    (0..).zip(members).find_map(|(j, m)| {
        if m.examples.contains(&index) {
            return Some(BodyOwner::Example);
        }
        match &m.kind {
            MemberKind::Fn(f) => holds(f.body, index).map(|hole| BodyOwner::Fn {
                name: f.name,
                signature: Box::new(signature(f, &owner(decl, Some(j)), self_ty, outer)),
                place: place.clone(),
                hole,
                limits: f.limits,
                procedural: f.procedural,
            }),
            MemberKind::Const(c) => {
                (c.value == index).then(|| BodyOwner::Const(c.ty.clone(), None))
            }
            MemberKind::TraitConst(_, ty, value) => {
                let trait_item = match place {
                    Place::Trait(t) => Some(t.clone()),
                    Place::Module | Place::Impl { .. } => None,
                };
                (*value == Some(index)).then(|| BodyOwner::Const(ty.clone(), trait_item))
            }
        }
    })
}

/// The name of a type parameter or row variable that a module declares.
pub(crate) fn generic_name(module: &ModuleHir, id: &GenericId) -> Option<Name> {
    if id.is_poly() {
        // A type parameter of a polymorphic function type (polymorphism.function-types).
        return module
            .poly_names
            .iter()
            .find(|(p, _)| *p == id.declared())
            .map(|(_, n)| *n);
    }
    let pick = |generics: &[Generic]| generics.get(id.index as usize).map(|g| g.name);
    let item = module.items.get(id.owner.decl.index as usize)?;
    match (item, id.owner.member) {
        (ItemHir::Decl(d), None) => match &d.kind {
            DeclKind::Fn(f) => pick(&f.generics),
            DeclKind::Type(t) => t.params.get(id.index as usize).copied(),
            DeclKind::Trait(t) => t.params.get(id.index as usize).copied(),
            _ => None,
        },
        (ItemHir::Decl(d), Some(j)) => match &d.kind {
            DeclKind::Trait(t) => member_generics(t.members.get(j as usize)?).and_then(pick),
            _ => None,
        },
        (ItemHir::Impl(imp), None) => pick(&imp.generics),
        (ItemHir::Impl(imp), Some(j)) => {
            member_generics(imp.members.get(j as usize)?).and_then(pick)
        }
        (ItemHir::Use, _) => None,
    }
}

fn member_generics(m: &stilt_hir::hir::Member) -> Option<&[Generic]> {
    match &m.kind {
        MemberKind::Fn(f) => Some(&f.generics),
        MemberKind::Const(_) | MemberKind::TraitConst(..) => None,
    }
}
