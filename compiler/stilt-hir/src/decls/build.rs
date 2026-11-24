//! Gathering the declarations of every module's items.

use stilt_db::SourceFile;
use stilt_diag::Code;

use super::signatures::{const_signature, signature};
use super::{
    DeclProblem, Declarations, EffectInfo, MemberKindInfo, OperationSig, TraitInfo, TraitMethod,
    TypeDefInfo, TypeInfo, VariantInfo, prelude_item,
};
use crate::Anchor;
use crate::hir::{
    Decl, DeclId, DeclKind, EffectDecl, GenericId, Item, ItemHir, Member, MemberKind, ModuleHir,
    Name, Owner, Param, TraitDecl, Ty, TypeDecl, TypeDef,
};
use crate::scope::PRELUDE;

/// The built-in types, with their numbers of type parameters. Each type parameter is that of
/// the declaration the type would have in the prelude.
fn builtin_types() -> impl Iterator<Item = (Item, Vec<GenericId>)> {
    let names = crate::scope::PRIMITIVE_TYPES
        .into_iter()
        .map(|name| (name, 0))
        .chain([("Never", 0), ("List", 1), ("Map", 2)]);
    names.map(|(name, arity)| {
        let owner = Owner {
            decl: DeclId {
                module: Name::from(format!("{PRELUDE}.{name}")),
                index: 0,
            },
            member: None,
        };
        let params = (0..arity)
            .map(|index| GenericId {
                owner: owner.clone(),
                index,
            })
            .collect();
        (prelude_item(name), params)
    })
}

/// A module with its file.
pub(super) struct Unit<'a> {
    pub(super) file: SourceFile,
    pub(super) path: &'a str,
    pub(super) hir: &'a ModuleHir,
}

impl Unit<'_> {
    pub(super) fn item(&self, name: Name) -> Item {
        Item {
            home: self.hir.name,
            name,
        }
    }

    pub(super) fn owner(&self, index: u32, member: Option<u32>) -> Owner {
        Owner {
            decl: DeclId {
                module: self.hir.name,
                index,
            },
            member,
        }
    }
}

pub(super) struct Builder {
    pub(super) decls: Declarations,
}

impl Builder {
    pub(super) fn problem(&mut self, unit: &Unit<'_>, at: Anchor, code: Code, message: String) {
        self.decls.problems.push(DeclProblem {
            file: unit.file,
            at,
            code,
            message,
        });
    }

    /// Declares the built-in types and every module's items.
    pub(super) fn declare_items(&mut self, units: &[Unit<'_>]) {
        for (item, params) in builtin_types() {
            let info = TypeInfo {
                params,
                values: Vec::new(),
                def: TypeDefInfo::Builtin,
                is_pub: true,
                pack: false,
            };
            self.decls.types.insert(item, info);
        }
        for unit in units {
            for (index, item) in (0..).zip(&unit.hir.items) {
                if let ItemHir::Decl(decl) = item {
                    self.declare(unit, index, decl);
                }
            }
        }
    }

    fn declare(&mut self, unit: &Unit<'_>, index: u32, decl: &Decl) {
        let owner = unit.owner(index, None);
        match &decl.kind {
            DeclKind::Fn(f) => {
                let s = signature(f, &owner, &Ty::Error, (&Vec::new(), &[]));
                self.decls.functions.entry(unit.item(f.name)).or_insert(s);
            }
            DeclKind::Const(c) => {
                let ty = c.ty.clone();
                self.decls.constants.entry(unit.item(c.name)).or_insert(ty);
            }
            DeclKind::Type(t) => self.declare_type(unit, &owner, t, decl.is_pub),
            DeclKind::Trait(t) => self.declare_trait(unit, index, t),
            DeclKind::Effect(e) => self.declare_effect(unit, &owner, e),
            DeclKind::Test(..) | DeclKind::Macro(_) => {}
        }
    }

    /// An effect, whose type parameters are those of its declaration (handlers.declaring-effect).
    fn declare_effect(&mut self, unit: &Unit<'_>, owner: &Owner, e: &EffectDecl) {
        let item = unit.item(e.name);
        if self.decls.effects.contains_key(&item) {
            return;
        }
        let params = (0..)
            .zip(&e.params)
            .map(|(index, _)| GenericId {
                owner: owner.clone(),
                index,
            })
            .collect();
        let ops = e
            .ops
            .iter()
            .map(|o| OperationSig {
                name: o.name,
                params: o.params.clone(),
                ret: o.ret.clone().unwrap_or(Ty::Tuple(Vec::new())),
                row: o.row.clone(),
            })
            .collect();
        self.decls.effects.insert(item, EffectInfo { params, ops });
    }

    fn declare_type(&mut self, unit: &Unit<'_>, owner: &Owner, t: &TypeDecl, is_pub: bool) {
        let item = unit.item(t.name);
        if self.decls.types.contains_key(&item) {
            return;
        }
        let params = (0..)
            .zip(&t.params)
            .map(|(index, _)| GenericId {
                owner: owner.clone(),
                index,
            })
            .collect();
        let def = match &t.def {
            TypeDef::Record(fields) => TypeDefInfo::Record(fields.clone()),
            TypeDef::Variants(variants) => {
                for (index, (name, payload)) in (0..).zip(variants) {
                    let info = VariantInfo {
                        ty: item.clone(),
                        index,
                        payload: payload.clone(),
                    };
                    self.decls.variants.entry(unit.item(*name)).or_insert(info);
                }
                TypeDefInfo::Variants(variants.clone())
            }
            // A native type is built in as `List` and `Map` are, its representation the
            // implementation's (views.std-view).
            TypeDef::Native => TypeDefInfo::Builtin,
        };
        let info = TypeInfo {
            params,
            values: t.values.clone(),
            def,
            is_pub,
            pack: t.pack,
        };
        self.decls.types.insert(item, info);
    }

    fn declare_trait(&mut self, unit: &Unit<'_>, index: u32, t: &TraitDecl) {
        let item = unit.item(t.name);
        if self.decls.traits.contains_key(&item) {
            return;
        }
        let owner = unit.owner(index, None);
        let params = (0..)
            .zip(&t.params)
            .map(|(index, _)| GenericId {
                owner: owner.clone(),
                index,
            })
            .collect();
        let methods = (0..)
            .zip(&t.members)
            .filter(|(_, m)| !m.unknown)
            .filter_map(|(j, m)| trait_member(&unit.owner(index, Some(j)), m))
            .collect();
        let unknown_methods = t
            .members
            .iter()
            .filter(|m| m.unknown)
            .map(|m| *m.name())
            .collect();
        self.decls.traits.insert(
            item.clone(),
            TraitInfo {
                params,
                arity: t.arity,
                methods,
                unknown_methods,
            },
        );
        self.decls
            .module_traits
            .entry(unit.hir.name)
            .or_default()
            .push(item);
    }
}

/// A member of a trait, declared by `owner`: a method, a function without `self`, or a
/// constant (traits.functions-without-self and traits.trait-constants).
fn trait_member(owner: &Owner, m: &Member) -> Option<TraitMethod> {
    match &m.kind {
        MemberKind::Fn(f) => Some(TraitMethod {
            name: f.name,
            kind: match f.params.first() {
                Some(Param::SelfParam(mode, _)) => MemberKindInfo::Method(*mode),
                _ => MemberKindInfo::Function,
            },
            signature: signature(f, owner, &Ty::SelfTy, (&Vec::new(), &[])),
            has_default: f.body.is_some(),
        }),
        MemberKind::TraitConst(name, ty, value) => Some(TraitMethod {
            name: *name,
            kind: MemberKindInfo::Constant,
            signature: const_signature(owner, &Vec::new(), ty),
            has_default: value.is_some(),
        }),
        MemberKind::Const(_) => None,
    }
}
