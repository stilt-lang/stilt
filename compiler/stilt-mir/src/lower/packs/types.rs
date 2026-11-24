//! Types with a pack (variadics.packs): the structural impls of `type Row<..Ts> = …` are
//! compiled, as a function is, for each arity of the pack that a use reaches, its environment
//! holding each element's witness and dictionaries, as a tuple's holds each element's.

use stilt_hir::decls::Lookup;
use stilt_hir::hir::{GenericId, Item};
use stilt_types::ty::Ty;

use super::super::Lower;
use super::{pack_element, static_elements};
use crate::Held;
use crate::mir::{Heapness, Local, Operand};

/// Whether the type constructor `item`'s last parameter is a pack.
pub(crate) fn has_pack(decls: &dyn Lookup, item: &Item) -> bool {
    decls.type_info(item).is_some_and(|t| t.pack)
}

/// The components of a structural impl's environment for a type of constructor `item` with the
/// arguments `args`: each argument, and each element of a pack's, or `None` for a pack whose
/// length its use doesn't know.
pub(crate) fn components(decls: &dyn Lookup, item: &Item, args: &[Ty]) -> Option<Vec<Ty>> {
    if !has_pack(decls, item) {
        return Some(args.to_vec());
    }
    let (last, rest) = args.split_last()?;
    let mut out = rest.to_vec();
    out.extend(static_elements(last)?);
    Some(out)
}

impl Lower<'_> {
    /// The environment of the structural impl of a type with a pack whose length its use knows
    /// at run time only: each other argument's witness and dictionaries, then the pack's lists
    /// (`super::super::dicts`).
    pub(crate) fn type_pack_env(&mut self, args: &[Ty]) -> Vec<(Operand, Heapness)> {
        let Some((last, rest)) = args.split_last() else {
            return Vec::new();
        };
        let mut env = Vec::new();
        for arg in rest {
            env.push((self.witness(arg), Heapness::Static(false)));
            for name in crate::lower::dicts::PRELUDE_TRAITS {
                let t = stilt_hir::decls::prelude_item(name);
                let d = if self.implements(arg, &t) {
                    self.dict(arg, &t)
                } else {
                    Operand::word(0)
                };
                env.push((d, Heapness::Static(true)));
            }
        }
        env.extend(self.pack_env(last));
        env
    }

    /// Gives a type's pack `g`, whose length the key doesn't know, the list of its elements'
    /// witnesses and the lists of their dictionaries for `traits`, fields of the data object
    /// `env` from field `*next` on, as a dynamic pack holds them (`super::dynamic`).
    fn dynamic_pack_from(
        &mut self,
        g: &GenericId,
        traits: &[Item],
        (env, len): (Local, u32),
        next: &mut u32,
    ) {
        let mut lists = Vec::new();
        for _ in 0..=traits.len() {
            lists.push(self.borrowed_field(env, len, *next, crate::mir::Repr::Heap));
            *next += 1;
        }
        self.push_dynamic_pack(
            g,
            lists[0],
            traits.iter().cloned().zip(lists[1..].iter().copied()),
        );
    }

    /// Takes the next generic of the key as a type's pack `g`, each of whose elements has the
    /// bounds `traits`, as a structural impl's parameter.
    pub(crate) fn add_type_pack(&mut self, g: &GenericId, traits: &[Item]) {
        self.add_pack_param(g, traits);
        self.b.hide();
    }

    /// Gives the type's pack `g` its elements' generics, their witnesses and dictionaries for
    /// `traits` fields of the data object `env` from field `*next` on, of `len` fields.
    pub(crate) fn type_pack_from(
        &mut self,
        g: &GenericId,
        traits: &[Item],
        (env, len): (Local, u32),
        next: &mut u32,
    ) {
        let Some(Held::Pack(Some(es))) = self.held.get(self.key_index()).cloned() else {
            self.cons.taken += 1;
            self.dynamic_pack_from(g, traits, (env, len), next);
            return;
        };
        self.cons.taken += 1;
        let mut types = Vec::new();
        for (i, key) in es.iter().enumerate() {
            let e = Ty::Param(pack_element(g, i));
            let mut parts = Vec::new();
            for _ in 0..=traits.len() {
                let repr = if parts.is_empty() {
                    crate::mir::Repr::Scalar
                } else {
                    crate::mir::Repr::Heap
                };
                parts.push(self.borrowed_field(env, len, *next, repr));
                *next += 1;
            }
            let dicts = traits
                .iter()
                .zip(&parts[1..])
                .map(|(t, d)| (t.clone(), crate::mir::Operand::Local(*d)))
                .collect();
            self.push_generic(e.clone(), parts[0], dicts, Some(key));
            self.cons.extra += 1;
            types.push(e);
        }
        self.cons.params.push((g.clone(), Ty::Tuple(types)));
    }
}
