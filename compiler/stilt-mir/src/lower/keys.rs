//! The keys of instances (goal inline-values): how the code of a generic
//! function holds the values of each of its type parameters, by their arguments' layouts,
//! whatever their size.
//!
//! A type parameter bounded by a trait with methods of their own type parameters is keyed by
//! its argument's constructor as well ([`crate::Known`]), and by the keys of the constructor's
//! arguments that the impls of those traits need, so that the instance calls those methods
//! directly, compiled for the layouts of their own type arguments, which a dictionary's entry,
//! compiled once for every caller, can't be.
//!
//! Generic code that calls itself with ever bigger types, which only polymorphic recursion
//! does, would have instances without end, so keys have caps, which apply only to a request
//! that an instance makes within its own cycle of the call graph ([`cycles`]) with a key bigger
//! than any of its own. Code that doesn't reach itself is compiled for its type arguments
//! however large or deeply nested. Within a cycle, a key knows at most [`MAX_KNOWN`]
//! constructors: past them, the instance calls such a method through the dictionary, whose
//! entry holds the method's own type parameters in one word. And a type argument that the
//! instance builds from its own type parameters with more than [`MAX_WORDS`] words crosses into
//! the callee's instance in its box. A call past the caps converts the values whose types hold
//! such an argument, and every program runs (`super::bridge`).

use std::sync::Arc;

use stilt_hir::decls::{Bounds, Lookup};
use stilt_hir::hir::Item;
use stilt_types::ty::Ty;

use super::cons::{con_key, is_constructor};
use super::functions::signature;
use super::{Generic, Lower};
use crate::items::ImplRef;
use crate::mir::{Element, Elements, Local, NumKind, Operand, Prim, Repr, Runtime, Rvalue};
use crate::{FnRef, Held, Known, Word};

mod cycles;

pub(crate) use cycles::{Node, edges, node_of};

/// The most constructors a key knows.
pub(crate) const MAX_KNOWN: usize = 16;

/// The most words of a type argument that an instance builds from its own type parameters
/// and holds inline in its callee's instance.
pub(crate) const MAX_WORDS: usize = 256;

/// Whether a trait has a method with type parameters of its own, or is a constructor trait,
/// whose constructor keys every instance.
/// A record bound keys its parameter by its record type's constructor (`super::records`).
pub(crate) fn keyed(decls: &dyn Lookup, t: &Item) -> bool {
    t.is_record_bound()
        || decls.trait_info(t).is_some_and(|info| {
            info.arity > 0
                || info
                    .methods
                    .iter()
                    .any(|m| !m.signature.type_params.is_empty())
        })
}

/// The traits among `traits` that key a type parameter they bound.
fn keying(decls: &dyn Lookup, traits: &[Item]) -> Vec<Item> {
    traits.iter().filter(|t| keyed(decls, t)).cloned().collect()
}

/// How a generic in scope is held, as a callee's key says it.
pub(crate) fn held_of(g: &Generic) -> Held {
    if let Some(v) = g.value {
        return Held::Value(v);
    }
    let held = match &g.held {
        None => Held::Word,
        Some(words) => Held::Words(words.iter().map(|&r| key_word(r)).collect()),
    };
    match &g.known {
        None => held,
        Some((con, args)) => Held::Impl(Arc::new(Known {
            held,
            con: con.clone(),
            args: args.clone(),
        })),
    }
}

impl Lower<'_> {
    /// The representations of the words of a key, each dynamic word's heapness the bit of the
    /// witness's mask for it, shifted to its lowest bit (`crate::shape`).
    pub(super) fn held_words(&mut self, witness: Local, words: &[Word]) -> Vec<Repr> {
        let large =
            words.iter().map(|&w| Element::words(w)).sum::<usize>() > crate::shape::MASK_WORDS;
        let mut at = 0;
        words
            .iter()
            .map(|&w| self.held_word(witness, w, &mut at, large))
            .collect()
    }

    /// The representation of a word of a key, word `at` of its argument's value, which it
    /// moves past: the words of an array held in memory are those of its first element, which
    /// every element's match.
    fn held_word(&mut self, witness: Local, w: Word, at: &mut usize, large: bool) -> Repr {
        let k = *at;
        *at += Element::words(w);
        match w {
            Word::Scalar => Repr::Scalar,
            Word::Heap => Repr::Heap,
            // The bit of word `k` in the witness's mask, or in the description of a large
            // shape's words, which the runtime reads.
            Word::Dynamic if large => {
                let args = vec![Operand::Local(witness), Operand::word(k as u64)];
                let bit = Rvalue::Runtime(Runtime::ShapeHeap, args);
                Repr::Generic(self.b.define(Repr::Scalar, bit))
            }
            Word::Dynamic => {
                let shift = u64::from(crate::shape::MASK_SHIFT) + k as u64;
                let args = vec![Operand::Local(witness), Operand::word(shift)];
                let bit = Rvalue::Prim(Prim::Shr(NumKind::U64), args, Operand::word(0));
                Repr::Generic(self.b.define(Repr::Scalar, bit))
            }
            Word::Array(e) => {
                let mut inner = k;
                let each = e
                    .each()
                    .iter()
                    .map(|&w| self.held_word(witness, w, &mut inner, large))
                    .collect();
                Repr::Array(Elements::new(e.len(), each))
            }
        }
    }

    /// How a value of type `ty` is held where a type parameter stands: in one word, or in the
    /// words of its layout.
    fn held_key(&self, ty: &Ty) -> Held {
        let layout = self.layout(ty);
        if super::words::one_word(&layout) {
            return Held::Word;
        }
        Held::Words(layout.iter().map(|&r| key_word(r)).collect())
    }

    /// The key of a type argument for a type parameter bounded by the traits `needs` that key
    /// it: how its values are held, and its constructor where `needs` has a trait, unless the
    /// key is `capped` and would know more than [`MAX_KNOWN`] constructors.
    pub(crate) fn key(&self, ty: &Ty, needs: &[Item], capped: bool) -> Held {
        if let Some(held) = self.value_key(ty) {
            return held;
        }
        if is_constructor(&self.decls(), needs) {
            return con_key(ty);
        }
        let held = self.held_key(ty);
        if needs.is_empty() {
            return held;
        }
        let key = match ty {
            Ty::Param(_) | Ty::SelfTy => return self.generic(ty).map_or(held, held_of),
            Ty::Con(con, args) => {
                let arg_needs = self.arg_needs(con, needs, args.len());
                let args: Box<[Held]> = args
                    .iter()
                    .zip(&arg_needs)
                    .map(|(a, n)| self.key(a, n, capped))
                    .collect();
                // An argument that the impls need known, but whose key doesn't know it, would
                // have the instance's calls go through its dictionary all the same.
                let unknown = args
                    .iter()
                    .zip(&arg_needs)
                    .any(|(a, n)| !n.is_empty() && !matches!(a, Held::Impl(_)));
                if unknown {
                    return held;
                }
                Held::Impl(Arc::new(Known {
                    held: held.clone(),
                    con: con.clone(),
                    args,
                }))
            }
            _ => return held,
        };
        if capped && key.knows() > MAX_KNOWN {
            held
        } else {
            key
        }
    }

    /// The traits that key each argument of constructor `con`, for the impls of `needs` that
    /// the constructor has: those that bound the impls' generics at the argument's place.
    fn arg_needs(&self, con: &Item, needs: &[Item], n: usize) -> Vec<Vec<Item>> {
        let decls = self.decls();
        let mut out = vec![Vec::new(); n];
        for t in needs {
            let Some(imp) = decls.trait_impl(t, con) else {
                continue;
            };
            let positions = super::targets::impl_positions(&imp.self_ty, &imp.generics);
            for ((_, bounds), k) in imp.generics.iter().zip(positions) {
                let Some(arg) = k.and_then(|k| out.get_mut(k)) else {
                    continue;
                };
                for b in keying(&decls, bounds) {
                    if !arg.contains(&b) {
                        arg.push(b);
                    }
                }
            }
        }
        out
    }

    /// The traits that key each of a function's generics, in the order of its hidden
    /// parameters.
    pub(crate) fn needs(&self, f: &FnRef) -> Vec<Vec<Item>> {
        let decls = self.decls();
        let bounds = |b: &Bounds| -> Vec<Vec<Item>> {
            b.iter().map(|(_, traits)| keying(&decls, traits)).collect()
        };
        match f.generic() {
            FnRef::Value(g) => self.needs(g),
            FnRef::Entry(imp, _) => match &**imp {
                ImplRef::Written { trait_item, owner } => decls
                    .trait_impl(trait_item, owner)
                    .map(|i| bounds(&i.generics))
                    .unwrap_or_default(),
                ImplRef::Structural { .. } => Vec::new(),
            },
            FnRef::Method(t, index) => {
                let mut needs = vec![keying(&decls, std::slice::from_ref(t))];
                if let Some(m) = decls
                    .trait_info(t)
                    .and_then(|info| info.methods.get(*index as usize).cloned())
                {
                    needs.extend(bounds(&m.signature.type_params));
                }
                needs
            }
            g => {
                let mut needs = Vec::new();
                if let FnRef::DefaultMethod(t, _) = g {
                    needs.push(keying(&decls, std::slice::from_ref(t)));
                    // The trait's parameters, after `Self`.
                    let params = decls.trait_info(t).map_or(0, |i| i.params.len());
                    needs.extend(std::iter::repeat_n(Vec::new(), params));
                }
                if let Some(sig) = signature(&decls, g) {
                    needs.extend(bounds(&sig.type_params));
                }
                needs
            }
        }
    }

    /// The code of `f`, a function whose generics are those of the types `targs`, in order:
    /// `f` itself where each is held in one word and keyed by no constructor, and otherwise its
    /// instance.
    pub(crate) fn instance(&self, f: FnRef, targs: &[Ty]) -> FnRef {
        let needs = self.needs(&f);
        let packs = self.pack_positions(&f);
        let values = self.value_positions(&f);
        let keys = |capped| -> Vec<Held> {
            targs
                .iter()
                .enumerate()
                .map(|(i, t)| {
                    let need = needs.get(i).map_or(&[][..], Vec::as_slice);
                    // A value parameter of another type than `i64` is passed alone.
                    if matches!(t, Ty::Value(_)) && !values.get(i).copied().unwrap_or(false) {
                        Held::Word
                    } else if packs.get(i).copied().unwrap_or(false) {
                        self.pack_key(&f, t, need, capped)
                    } else {
                        self.key(t, need, capped)
                    }
                })
                .collect()
        };
        let held = keys(false);
        if self.past_known(&held, &f) {
            let capped = keys(true);
            return FnRef::instance(f, capped);
        }
        FnRef::instance(f, held)
    }

    /// Whether a request of code of `callee` with keys `held` is past the cap of constructors:
    /// one of them knows more than [`MAX_KNOWN`] constructors and more than any key of this
    /// function's own, and the request is made within this function's cycle of the call graph,
    /// the only place where keys can grow without end.
    pub(crate) fn past_known(&self, held: &[Held], callee: &FnRef) -> bool {
        let own = self.held.iter().map(Held::knows).max().unwrap_or(0);
        held.iter().any(|h| h.knows() > MAX_KNOWN.max(own)) && self.in_cycle(callee)
    }

    /// The most words that a key of this function's own holds a value in.
    pub(crate) fn widest_key(&self) -> usize {
        let words = |h: &Held| match h.layout() {
            Held::Words(words) => words.iter().map(|&w| crate::mir::Element::words(w)).sum(),
            _ => 1,
        };
        self.held.iter().map(words).max().unwrap_or(1)
    }
}

/// What a word of a layout holds, as an instance's key says it.
pub(crate) fn key_word(r: Repr) -> Word {
    match r {
        Repr::Scalar => Word::Scalar,
        Repr::Heap => Word::Heap,
        Repr::Generic(_) => Word::Dynamic,
        Repr::Array(e) => Word::Array(
            e.map(|r| Some(key_word(r)))
                .expect("every word has a key's word"),
        ),
    }
}

#[cfg(test)]
mod tests;
