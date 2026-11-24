//! Looking declarations up through queries, each at most once in a query. A body names the
//! same few declarations many times, and each lookup through the database finds its key among
//! every thread's (Compiler architecture, "Queries"), so a query that checks a body keeps what
//! it found. It depends on each declaration it read all the same, since the database recorded
//! the first lookup.

use std::cell::RefCell;

use rustc_hash::FxHashMap as HashMap;
use stilt_db::{Db, Program};

use super::lookup::{function, inherent_members, trait_impl, type_info, variant};
use super::{FnSig, ImplInfo, Lookup, MemberInfo, Queried, TraitInfo, TypeInfo, VariantInfo};
use crate::hir::{Item, Name, Ty};

/// What a query has looked up, by declaration.
#[derive(Default)]
struct Found<'db> {
    types: HashMap<Item, Option<&'db TypeInfo>>,
    variants: HashMap<Item, Option<&'db VariantInfo>>,
    functions: HashMap<Item, Option<&'db FnSig>>,
    /// By trait, then by type constructor.
    impls: HashMap<Item, HashMap<Item, Option<&'db ImplInfo>>>,
    members: HashMap<Item, &'db [MemberInfo]>,
}

/// The declarations of a program, looked up through queries, each at most once.
pub struct QueriedOnce<'db> {
    queried: Queried<'db>,
    found: RefCell<Found<'db>>,
}

impl std::fmt::Debug for QueriedOnce<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.queried.fmt(f)
    }
}

impl<'db> QueriedOnce<'db> {
    /// The declarations of `program`, looked up through `db`.
    #[must_use]
    pub fn new(db: &'db dyn Db, program: Program) -> Self {
        Self {
            queried: Queried { db, program },
            found: RefCell::default(),
        }
    }
}

/// The value of `key` in the map that `field` picks, found by `look` the first time.
fn once<'db, K, V>(
    found: &RefCell<Found<'db>>,
    field: for<'a> fn(&'a mut Found<'db>) -> &'a mut HashMap<K, V>,
    key: &K,
    look: impl FnOnce() -> V,
) -> V
where
    K: std::hash::Hash + Eq + Clone,
    V: Copy,
{
    if let Some(&value) = field(&mut found.borrow_mut()).get(key) {
        return value;
    }
    let value = look();
    field(&mut found.borrow_mut()).insert(key.clone(), value);
    value
}

impl Lookup for QueriedOnce<'_> {
    fn type_info(&self, item: &Item) -> Option<&TypeInfo> {
        if item.is_record() {
            return super::records::record_info(item);
        }
        let Queried { db, program } = self.queried;
        once(
            &self.found,
            |f| &mut f.types,
            item,
            || type_info(db, program, item.clone()).as_ref(),
        )
    }

    fn variant(&self, item: &Item) -> Option<&VariantInfo> {
        let Queried { db, program } = self.queried;
        once(
            &self.found,
            |f| &mut f.variants,
            item,
            || variant(db, program, item.clone()).as_ref(),
        )
    }

    fn function(&self, item: &Item) -> Option<&FnSig> {
        let Queried { db, program } = self.queried;
        once(
            &self.found,
            |f| &mut f.functions,
            item,
            || function(db, program, item.clone()).as_ref(),
        )
    }

    fn constant(&self, item: &Item) -> Option<&Ty> {
        self.queried.constant(item)
    }

    fn trait_info(&self, item: &Item) -> Option<&TraitInfo> {
        self.queried.trait_info(item)
    }

    fn effect_info(&self, item: &Item) -> Option<&super::EffectInfo> {
        self.queried.effect_info(item)
    }

    fn trait_impl(&self, trait_item: &Item, owner: &Item) -> Option<&ImplInfo> {
        let known = (self.found.borrow().impls)
            .get(trait_item)
            .and_then(|of| of.get(owner).copied());
        if let Some(found) = known {
            return found;
        }
        let Queried { db, program } = self.queried;
        let found = trait_impl(db, program, trait_item.clone(), owner.clone()).as_ref();
        let mut all = self.found.borrow_mut();
        let of_trait = all.impls.entry(trait_item.clone()).or_default();
        of_trait.insert(owner.clone(), found);
        found
    }

    fn inherent_members(&self, owner: &Item) -> &[MemberInfo] {
        let Queried { db, program } = self.queried;
        once(
            &self.found,
            |f| &mut f.members,
            owner,
            || inherent_members(db, program, owner.clone()),
        )
    }

    fn module_traits(&self, module: &str) -> &[Item] {
        self.queried.module_traits(module)
    }

    fn broken(&self) -> &[(Option<Item>, Name)] {
        self.queried.broken()
    }
}
