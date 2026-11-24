//! Records that no declaration names (records.update and records.record-bounds): update syntax, and
//! record bounds.
//!
//! A record bound passes where its fields are in the record's layout. Here it
//! keys the instance by the record type's constructor ([`crate::Known`]), as a trait whose
//! methods have type parameters of their own does (`super::keys`): the instance is compiled
//! for that constructor, with every type that names the bounded parameter retyped with it, so
//! it reads and writes the fields where the record's layout has them. The constructor's
//! arguments stay generic, each with a witness that the caller passes and held as the key says.

use stilt_hir::hir::{DeclId, GenericId, Item, Name, Owner};
use stilt_types::tast::Expr;
use stilt_types::ty::Ty;

use super::Lower;
use crate::Held;
use crate::mir::Operand;

/// Whether a type parameter's bounds hold a record bound.
pub(crate) fn has_record_bound(traits: &[Item]) -> bool {
    traits.iter().any(Item::is_record_bound)
}

/// The bounds of a type parameter that dictionaries stand for: all but its record bounds.
pub(crate) fn dict_bounds(traits: &[Item]) -> Vec<Item> {
    traits
        .iter()
        .filter(|t| !t.is_record_bound())
        .cloned()
        .collect()
}

/// The generic that stands for argument `i` of the record type that the instance's key gives
/// the record-bounded parameter `g`.
fn record_arg(g: &GenericId, i: usize) -> GenericId {
    let i = u32::try_from(i).expect("under 4G arguments");
    GenericId {
        owner: Owner {
            decl: DeclId {
                module: format!(
                    "#record:{}:{}:{}",
                    g.owner.decl.module, g.owner.decl.index, g.index
                )
                .into(),
                index: g.owner.member.unwrap_or(u32::MAX),
            },
            member: None,
        },
        index: i,
    }
}

impl Lower<'_> {
    /// Takes the next generic of the instance's key as the record-bounded parameter `g`'s:
    /// the code is retyped with the key's record type for it, whose arguments are generics of
    /// their own.
    pub(crate) fn add_record_param(&mut self, g: &GenericId) {
        let index = self.key_index();
        self.cons.taken += 1;
        let Some(Held::Impl(known)) = self.held.get(index).cloned() else {
            self.cons.params.push((g.clone(), Ty::Error));
            return;
        };
        let mut args = Vec::new();
        for (i, held) in known.args.iter().enumerate() {
            let arg = Ty::Param(record_arg(g, i));
            self.add_generic_held(arg.clone(), &[], Some(held));
            self.cons.extra += 1;
            args.push(arg);
        }
        self.cons
            .params
            .push((g.clone(), Ty::Con(known.con.clone(), args)));
    }

    /// The hidden arguments for a record-bounded parameter instantiated with `ty`: a witness
    /// for each argument of its record type.
    pub(crate) fn record_args(&mut self, ty: &Ty) -> Vec<Operand> {
        match ty {
            Ty::Con(_, args) => args.iter().map(|a| self.witness(a)).collect(),
            _ => Vec::new(),
        }
    }

    /// `{ ..base, f: e }`: `base` evaluated first, then the fields in written order, and the
    /// fields not written copied from `base` (records.update).
    pub(crate) fn update(&mut self, base: &Expr, given: &[(Name, Expr)], ty: &Ty) -> Vec<Operand> {
        let b = self.expr(base);
        let values: Vec<(Name, Vec<Operand>)> =
            given.iter().map(|(n, x)| (*n, self.expr(x))).collect();
        let declared = match ty {
            Ty::Con(item, _) => self.field_names(item),
            _ => Vec::new(),
        };
        let fields = self.fields_of(ty, 0);
        let in_order = declared
            .iter()
            .enumerate()
            .map(|(j, n)| match values.iter().find(|(m, _)| m == n) {
                Some((_, v)) => v.clone(),
                None => self.field_words(&b, &fields, j),
            })
            .collect();
        self.build(ty, 0, in_order)
    }
}
