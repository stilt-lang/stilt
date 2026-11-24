//! Whether a module uses the traits of traits.trait-parameters, which puts it in the advanced tier
//! (traits.advanced-tier; program.module-tier).

use stilt_db::{Db, Program};
use stilt_hir::decls::{Bounds, Declarations, FnSig, TraitInfo, declarations};
use stilt_hir::hir::Item;

/// Whether `module` declares a trait with parameters, a trait function without `self`, a
/// trait constant or a constructor trait, writes an impl of one, or names one in a bound
/// (traits.advanced-tier). A member type and a `where` clause each need such a bound, of the
/// module's own declarations, so they are found through it. Calling a method of such a trait
/// doesn't make a module advanced.
#[must_use]
pub fn uses_parameters(db: &dyn Db, program: Program, module: &str) -> bool {
    let decls = declarations(db, program);
    let ours = |item: &Item| &*item.home == module;
    let declares = decls
        .traits
        .iter()
        .any(|(item, info)| ours(item) && is_advanced(info));
    let implements = decls
        .trait_impls
        .iter()
        .any(|((t, _), imp)| &*imp.module == module && advanced(decls, t));
    let bounds = |b: &Bounds| {
        b.iter()
            .any(|(_, traits)| traits.iter().any(|t| advanced(decls, t)))
    };
    let sig = |s: &FnSig| bounds(&s.type_params);
    let functions = decls.functions.iter().any(|(i, s)| ours(i) && sig(s));
    let members = decls
        .inherent
        .iter()
        .filter(|(owner, _)| ours(owner))
        .any(|(_, ms)| ms.iter().any(|m| sig(&m.signature)));
    let impls = decls
        .trait_impls
        .values()
        .filter(|i| &*i.module == module)
        .any(|i| bounds(&i.generics) || i.members.iter().any(|m| sig(&m.signature)));
    let traits = decls
        .traits
        .iter()
        .filter(|(item, _)| ours(item))
        .any(|(_, t)| t.methods.iter().any(|m| sig(&m.signature)));
    declares || implements || functions || members || impls || traits
}

/// Whether a trait is one of those of the advanced tier: one with parameters, a constructor trait,
/// or one with a function without `self` or a constant.
fn is_advanced(info: &TraitInfo) -> bool {
    !info.params.is_empty() || info.arity > 0 || info.methods.iter().any(|m| !m.is_method())
}

fn advanced(decls: &Declarations, t: &Item) -> bool {
    decls.traits.get(t).is_some_and(is_advanced)
}
