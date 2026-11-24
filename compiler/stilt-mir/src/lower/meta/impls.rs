//! A descriptor's table of impls (meta.bound-tests): the dictionary of each trait of the
//! table, or 0 where the type has no impl of it, which a bound test looks up. The type of a
//! descriptor's code may hold type parameters, whose descriptors' tables give their impls: an
//! impl that needs one of theirs is in the table only where each it needs is there.
//!
//! A table holds no code compiled for its type alone. The structural impl of a tuple, a record,
//! a variant type or an array is a shape dictionary, whose methods walk the descriptor's parts
//! for every type of that shape ([`super::shaped`]); the one of a list, a map, a set or an
//! option is compiled for the layouts of its type arguments, with the dictionaries of each in
//! its environment taken from that argument's own table.

use stilt_hir::decls::{Lookup, prelude_item};
use stilt_hir::hir::Item;
use stilt_types::ty::Ty;

use super::{DESC_LEN, IMPLS};
use crate::items::{ImplRef, Shape};
use crate::lower::Lower;
use crate::lower::dicts::PRELUDE_TRAITS;
use crate::lower::traits::primitive;
use crate::mir::{Const, Heapness, Operand, Repr, Rvalue};

/// What a descriptor holds of its type that the shape dictionaries of its table hold too: the
/// case of its shape, its witness, and the four fields of its case.
pub(crate) struct Parts<'p> {
    pub(crate) case: Option<&'static str>,
    pub(crate) witness: &'p Operand,
    pub(crate) fields: &'p [(Operand, Heapness); 4],
}

impl Lower<'_> {
    /// The table of a type's impls, and the identities of the arguments each gives its trait.
    pub(crate) fn impls(&mut self, ty: &Ty, parts: &Parts<'_>) -> (Operand, Operand) {
        let traits = self.table_traits();
        let mut dicts = Vec::new();
        let mut args = Vec::new();
        for t in &traits {
            dicts.push((self.impl_entry(ty, t, parts), Heapness::Static(true)));
            args.push((self.impl_args_ident(ty, t), Heapness::Static(true)));
        }
        (self.alloc(0, dicts), self.alloc(0, args))
    }

    /// The table of a type that has no impls.
    pub(crate) fn no_impls(&mut self) -> (Operand, Operand) {
        let n = self.table_traits().len();
        let dicts = vec![(Operand::word(0), Heapness::Static(true)); n];
        let none = Operand::Const(Const::Str("".into()));
        let args = vec![(none, Heapness::Static(true)); n];
        (self.alloc(0, dicts), self.alloc(0, args))
    }

    /// The identities of the arguments that `ty`'s impl of `t` gives the trait's parameters,
    /// joined by `;`: "" for a trait without parameters, and where it has no impl.
    fn impl_args_ident(&mut self, ty: &Ty, t: &Item) -> Operand {
        let arity = self.decls().trait_info(t).map_or(0, |i| i.params.len());
        if arity == 0 || !self.implements(ty, t) {
            return Operand::Const(Const::Str("".into()));
        }
        let args = self.trait_args_of(ty, t);
        let pieces = Self::numbered_ident(&args);
        self.joined(&pieces, None, super::IDENT)
    }

    fn impl_entry(&mut self, ty: &Ty, t: &Item, parts: &Parts<'_>) -> Operand {
        if !self.implements(ty, t) {
            return Operand::word(0);
        }
        let needed = self.needed(ty, t);
        if needed.is_empty() {
            return self.table_dict(ty, t, parts);
        }
        let mut all = Operand::word(1);
        for d in needed {
            let none = self.word_eq(d, Operand::word(0));
            let some = self.not(none);
            all = self.both(all, some);
        }
        let result = self.b.temp(Repr::Heap);
        let (has, lacks, join) = (self.b.new_block(), self.b.new_block(), self.b.new_block());
        self.b.branch(all, has, lacks);
        self.b.switch_to(has);
        let dict = self.table_dict(ty, t, parts);
        self.b.assign(result, Rvalue::Use(dict));
        self.b.goto(join);
        self.b.switch_to(lacks);
        self.b.assign(result, Rvalue::Use(Operand::word(0)));
        self.b.goto(join);
        self.b.switch_to(join);
        Operand::Local(result)
    }

    /// The dictionaries of the type parameters in scope without which `ty` has no impl of `t`.
    fn needed(&self, ty: &Ty, t: &Item) -> Vec<Operand> {
        let decls = self.decls();
        let bounds = self.bounds();
        let mut out = Vec::new();
        for (i, (g, traits)) in bounds.iter().enumerate() {
            for tr in traits {
                let mut fewer = bounds.clone();
                fewer[i].1.retain(|x| x != tr);
                let scope = (&fewer, self.bound_args.as_slice());
                if stilt_types::implements_trait(&decls as &dyn Lookup, scope, ty, t) {
                    continue;
                }
                let dict = self
                    .generic(g)
                    .and_then(|held| held.dicts.iter().find(|(x, _)| x == tr))
                    .map(|(_, d)| d.clone());
                out.extend(dict);
            }
        }
        out
    }

    /// The dictionary of `ty`, which has an impl of `t`, that its table holds: a shape
    /// dictionary for the structural impl of a tuple, a record, a variant type or an array, the
    /// impl of another structural type with the dictionaries of its type arguments from their
    /// tables, and any other impl's own dictionary.
    fn table_dict(&mut self, ty: &Ty, t: &Item, parts: &Parts<'_>) -> Operand {
        let Some(imp) = self.walked(ty, t) else {
            return self.dict(ty, t);
        };
        if let Some(walk) = super::shaped::walk_of(parts.case) {
            return self.shape_dict(ty, t, walk, parts);
        }
        match self.table_env(ty) {
            Some(env) => self.impl_dict(&imp, ty, env),
            None => self.dict(ty, t),
        }
    }

    /// The structural impl of a prelude trait that a table holds in place of the dictionary
    /// compiled for `ty`, if `ty` has one: not a type parameter's, a primitive type's, a view's
    /// or that of a type with a pack, which keep their own.
    fn walked(&self, ty: &Ty, t: &Item) -> Option<ImplRef> {
        let prelude = PRELUDE_TRAITS.iter().any(|n| prelude_item(n) == *t);
        if !prelude || primitive(ty) || ty.viewed().is_some() || self.generic(ty).is_some() {
            return None;
        }
        let imp = self.impl_of(t, ty)?;
        let walked = match &imp {
            ImplRef::Structural {
                shape: Shape::Con(item),
                ..
            } => !crate::lower::packs::has_pack(&self.decls(), item),
            ImplRef::Structural {
                shape: Shape::Tuple(_),
                ..
            } => true,
            _ => false,
        };
        walked.then_some(imp)
    }

    /// The environment of the structural impl of `ty`, as [`Lower::structural_env`] gives it,
    /// but with the dictionaries of each of its type arguments that has a structural impl
    /// taken from the argument's table, or 0 for a trait that the table lacks: a structural
    /// impl calls its arguments' impls of its own trait alone, and `Hash` of a map's keys,
    /// which every table holds.
    fn table_env(&mut self, ty: &Ty) -> Option<Vec<(Operand, Heapness)>> {
        let Ty::Con(_, args) = ty else {
            return None;
        };
        let traits = self.table_traits();
        let tlen = u32::try_from(traits.len()).expect("under 4G traits");
        let mut env = Vec::new();
        for arg in args {
            env.push((self.witness(arg), Heapness::Static(false)));
            let mut table: Option<Operand> = None;
            for name in PRELUDE_TRAITS {
                let t = prelude_item(name);
                let at = traits.iter().position(|x| *x == t);
                let d = match (self.walked(arg, &t), at) {
                    _ if !self.implements(arg, &t) => Operand::word(0),
                    (None, _) => self.dict(arg, &t),
                    (Some(_), None) => Operand::word(0),
                    (Some(_), Some(j)) => {
                        let impls = if let Some(impls) = &table {
                            impls.clone()
                        } else {
                            let desc = self.descriptor(arg);
                            let impls = self.read(desc, DESC_LEN, IMPLS, Repr::Heap);
                            table.insert(impls).clone()
                        };
                        let j = u32::try_from(j).expect("under 4G traits");
                        self.read(impls, tlen, j, Repr::Heap)
                    }
                };
                env.push((d, Heapness::Static(true)));
            }
        }
        Some(env)
    }
}
