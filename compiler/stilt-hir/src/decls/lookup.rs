//! Looking declarations up one at a time. A query that reads one through [`Lookup`] depends on
//! that declaration alone, so that an edit of a signature checks again only what reads it
//! (goal edit-to-diagnostics).

#![expect(
    clippy::needless_pass_by_value,
    reason = "a query's arguments are its key, which salsa takes by value"
)]
#![expect(
    clippy::drop_non_drop,
    reason = "salsa's macro drops each query's key, which an item's interned names leave with \
              nothing to free"
)]

use stilt_db::{Db, Program};

use super::records::record_info;
use super::{
    Declarations, EffectInfo, FnSig, ImplInfo, MemberInfo, TraitInfo, TypeInfo, VariantInfo,
    declarations,
};
use crate::hir::{Item, Name, Ty};

/// What every item and impl block declares, one declaration at a time.
pub trait Lookup {
    /// A type.
    fn type_info(&self, item: &Item) -> Option<&TypeInfo>;
    /// A variant.
    fn variant(&self, item: &Item) -> Option<&VariantInfo>;
    /// A function's signature.
    fn function(&self, item: &Item) -> Option<&FnSig>;
    /// A constant's type.
    fn constant(&self, item: &Item) -> Option<&Ty>;
    /// A trait.
    fn trait_info(&self, item: &Item) -> Option<&TraitInfo>;
    /// An effect (handlers.declaring-effect).
    fn effect_info(&self, item: &Item) -> Option<&EffectInfo>;
    /// The impl of a trait, first, for a type constructor, second.
    fn trait_impl(&self, trait_item: &Item, owner: &Item) -> Option<&ImplInfo>;
    /// The members of a type's inherent impl blocks, in source order.
    fn inherent_members(&self, owner: &Item) -> &[MemberInfo];
    /// The traits a module declares, in source order.
    fn module_traits(&self, module: &str) -> &[Item];
    /// The members of impl blocks with errors, whose uses have the error type (errors.error-type),
    /// by type constructor where it is known.
    fn broken(&self) -> &[(Option<Item>, Name)];
}

impl Lookup for Declarations {
    fn type_info(&self, item: &Item) -> Option<&TypeInfo> {
        self.types.get(item).or_else(|| record_info(item))
    }

    fn variant(&self, item: &Item) -> Option<&VariantInfo> {
        self.variants.get(item)
    }

    fn function(&self, item: &Item) -> Option<&FnSig> {
        self.functions.get(item)
    }

    fn constant(&self, item: &Item) -> Option<&Ty> {
        self.constants.get(item)
    }

    fn trait_info(&self, item: &Item) -> Option<&TraitInfo> {
        self.traits.get(item)
    }

    fn effect_info(&self, item: &Item) -> Option<&EffectInfo> {
        self.effects.get(item)
    }

    fn trait_impl(&self, trait_item: &Item, owner: &Item) -> Option<&ImplInfo> {
        Declarations::trait_impl(self, trait_item, owner)
    }

    fn inherent_members(&self, owner: &Item) -> &[MemberInfo] {
        Declarations::inherent_members(self, owner)
    }

    fn module_traits(&self, module: &str) -> &[Item] {
        self.module_traits.get(module).map_or(&[], Vec::as_slice)
    }

    fn broken(&self) -> &[(Option<Item>, Name)] {
        &self.broken
    }
}

#[salsa::tracked(returns(ref))]
pub(super) fn type_info(db: &dyn Db, program: Program, item: Item) -> Option<TypeInfo> {
    declarations(db, program).types.get(&item).cloned()
}

#[salsa::tracked(returns(ref))]
pub(super) fn variant(db: &dyn Db, program: Program, item: Item) -> Option<VariantInfo> {
    declarations(db, program).variants.get(&item).cloned()
}

#[salsa::tracked(returns(ref))]
pub(super) fn function(db: &dyn Db, program: Program, item: Item) -> Option<FnSig> {
    declarations(db, program).functions.get(&item).cloned()
}

#[salsa::tracked(returns(ref))]
fn constant(db: &dyn Db, program: Program, item: Item) -> Option<Ty> {
    declarations(db, program).constants.get(&item).cloned()
}

#[salsa::tracked(returns(ref))]
fn trait_info(db: &dyn Db, program: Program, item: Item) -> Option<TraitInfo> {
    declarations(db, program).traits.get(&item).cloned()
}

#[salsa::tracked(returns(ref))]
fn effect_info(db: &dyn Db, program: Program, item: Item) -> Option<EffectInfo> {
    declarations(db, program).effects.get(&item).cloned()
}

#[salsa::tracked(returns(ref))]
pub(super) fn trait_impl(
    db: &dyn Db,
    program: Program,
    trait_item: Item,
    owner: Item,
) -> Option<ImplInfo> {
    declarations(db, program)
        .trait_impl(&trait_item, &owner)
        .cloned()
}

#[salsa::tracked(returns(ref))]
pub(super) fn inherent_members(db: &dyn Db, program: Program, owner: Item) -> Vec<MemberInfo> {
    declarations(db, program).inherent_members(&owner).to_vec()
}

#[salsa::tracked(returns(ref))]
fn module_traits(db: &dyn Db, program: Program, module: Name) -> Vec<Item> {
    declarations(db, program)
        .module_traits
        .get(&module)
        .cloned()
        .unwrap_or_default()
}

#[salsa::tracked(returns(ref))]
fn broken(db: &dyn Db, program: Program) -> Vec<(Option<Item>, Name)> {
    declarations(db, program).broken.clone()
}

/// The declarations of a program, looked up through queries, one for each declaration.
#[derive(Clone, Copy)]
pub struct Queried<'db> {
    /// The database it queries.
    pub db: &'db dyn Db,
    /// The program whose declarations it looks up.
    pub program: Program,
}

impl std::fmt::Debug for Queried<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Queried")
            .field("program", &self.program)
            .finish_non_exhaustive()
    }
}

impl Lookup for Queried<'_> {
    fn type_info(&self, item: &Item) -> Option<&TypeInfo> {
        if item.is_record() {
            return record_info(item);
        }
        type_info(self.db, self.program, item.clone()).as_ref()
    }

    fn variant(&self, item: &Item) -> Option<&VariantInfo> {
        variant(self.db, self.program, item.clone()).as_ref()
    }

    fn function(&self, item: &Item) -> Option<&FnSig> {
        function(self.db, self.program, item.clone()).as_ref()
    }

    fn constant(&self, item: &Item) -> Option<&Ty> {
        constant(self.db, self.program, item.clone()).as_ref()
    }

    fn trait_info(&self, item: &Item) -> Option<&TraitInfo> {
        trait_info(self.db, self.program, item.clone()).as_ref()
    }

    fn effect_info(&self, item: &Item) -> Option<&EffectInfo> {
        effect_info(self.db, self.program, item.clone()).as_ref()
    }

    fn trait_impl(&self, trait_item: &Item, owner: &Item) -> Option<&ImplInfo> {
        trait_impl(self.db, self.program, trait_item.clone(), owner.clone()).as_ref()
    }

    fn inherent_members(&self, owner: &Item) -> &[MemberInfo] {
        inherent_members(self.db, self.program, owner.clone())
    }

    fn module_traits(&self, module: &str) -> &[Item] {
        module_traits(self.db, self.program, Name::from(module))
    }

    fn broken(&self) -> &[(Option<Item>, Name)] {
        broken(self.db, self.program)
    }
}
