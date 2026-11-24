//! Converting a value into code past the caps, where each crossing type argument is held in its
//! box, and back (`super`). A composite converts field by field; a list or a map whose element
//! type holds a crossing argument other than as the element itself is rebuilt, as code past the
//! caps reads and writes an element of a crossing argument through the runtime, by the shape the
//! list or the map keeps; a value of a recursive type whose nodes hold a crossing argument has
//! its nodes rebuilt by a function the compiler makes ([`crate::FnRef::Rebuild`]); and a closure
//! is held by one that converts what it takes and gives ([`crate::FnRef::Adapt`]).

use std::collections::HashSet;

use stilt_hir::hir::Item;
use stilt_types::ty::{Ty, is_prelude};

use super::Dir;
use crate::lower::Lower;
use crate::lower::lists::element_of;
use crate::lower::places::key_ty;
use crate::lower::words::{operands, word};
use crate::mir::{NumKind, Operand, Prim, Repr, Runtime, Rvalue, Terminator};

/// The type a value converts from and the type it converts to.
fn sides<'t>(n: &'t Ty, u: &'t Ty, dir: Dir) -> (&'t Ty, &'t Ty) {
    match dir {
        Dir::In => (n, u),
        Dir::Out => (u, n),
    }
}

impl Lower<'_> {
    /// The type that code outside holds a crossing argument's generic `u` as, if it is one.
    pub(crate) fn crossing_of(&self, u: &Ty) -> Option<Ty> {
        self.crossing
            .iter()
            .find(|(g, _)| g == u)
            .map(|(_, n)| n.clone())
    }

    /// Whether a value of type `n` outside is held differently past the caps, as `u`.
    pub(crate) fn converts(&self, n: &Ty, u: &Ty) -> bool {
        self.converts_seen(n, u, &mut HashSet::new())
    }

    fn converts_seen(&self, n: &Ty, u: &Ty, seen: &mut HashSet<Item>) -> bool {
        if self.crossing_of(u).is_some() {
            return true;
        }
        match (n, u) {
            (Ty::Tuple(ns), Ty::Tuple(us)) => ns
                .iter()
                .zip(us)
                .any(|(n, u)| self.converts_seen(n, u, seen)),
            (Ty::Con(item, ns), Ty::Con(_, us)) => {
                if is_prelude(item, "List") || is_prelude(item, "Map") {
                    // The element of a crossing argument itself goes through the runtime.
                    return ns.iter().zip(us).any(|(n, u)| {
                        self.crossing_of(u).is_none() && self.converts_seen(n, u, seen)
                    });
                }
                if !seen.insert(item.clone()) {
                    return false;
                }
                let count = self.templates.of(item).variants.len().max(1);
                let any = (0..count).any(|v| {
                    let (nf, uf) = (self.fields_of(n, v), self.fields_of(u, v));
                    nf.all
                        .iter()
                        .zip(&uf.all)
                        .any(|(a, b)| self.converts_seen(&a.ty, &b.ty, seen))
                });
                seen.remove(item);
                any
            }
            (Ty::Fn(nf), Ty::Fn(uf)) => {
                nf.params
                    .iter()
                    .zip(&uf.params)
                    .any(|((_, a), (_, b))| self.converts_seen(a, b, seen))
                    || self.converts_seen(&nf.ret, &uf.ret, seen)
                    || match (&nf.row.raise, &uf.row.raise) {
                        (Some(a), Some(b)) => self.converts_seen(a, b, seen),
                        _ => false,
                    }
            }
            _ => false,
        }
    }

    /// The words of a value of type `n` outside, as `u` past the caps, converted in direction
    /// `dir` from the words given, which it consumes.
    pub(crate) fn cross_convert(
        &mut self,
        words: Vec<Operand>,
        n: &Ty,
        u: &Ty,
        dir: Dir,
    ) -> Vec<Operand> {
        if n == u || !self.converts(n, u) {
            return words;
        }
        if let Some(inner) = self.crossing_of(u) {
            return match dir {
                Dir::In => {
                    let words = self.cross_convert(words, n, &inner, dir);
                    vec![self.boxed(words, &inner)]
                }
                Dir::Out => {
                    let words = self.unbox(word(&words, 0), &inner);
                    self.cross_convert(words, n, &inner, dir)
                }
            };
        }
        match n {
            Ty::Tuple(_) => self.convert_variant(&words, n, u, dir, 0),
            Ty::Con(item, _) if is_prelude(item, "List") => self.convert_list(&words, n, u, dir),
            Ty::Con(item, _) if is_prelude(item, "Map") => self.convert_map(&words, n, u, dir),
            Ty::Con(item, _) if self.templates.heap(item) => self.rebuild(words, n, u, dir),
            Ty::Con(..) => self.convert_variants(&words, n, u, dir),
            Ty::Fn(_) => self.adapt(&words, n, u, dir),
            _ => words,
        }
    }

    /// A value of a declared type converted variant by variant: one level of its nodes, for a
    /// recursive type, whose fields of that type the function that rebuilds it converts.
    pub(crate) fn convert_variants(
        &mut self,
        words: &[Operand],
        n: &Ty,
        u: &Ty,
        dir: Dir,
    ) -> Vec<Operand> {
        let Ty::Con(item, _) = n else {
            return words.to_vec();
        };
        let count = self.templates.of(item).variants.len().max(1);
        let (from, to) = sides(n, u, dir);
        if count == 1 && self.fields_of(from, 0).object.is_none() {
            return self.convert_variant(words, n, u, dir, 0);
        }
        let out = self.temps(to);
        let join = self.b.new_block();
        for v in 0..count {
            let (this, next) = (self.b.new_block(), self.b.new_block());
            let index = u32::try_from(v).expect("under 4G variants");
            let is = self.is_variant(words, from, index);
            self.b.branch(is, this, next);
            self.b.switch_to(this);
            let converted = self.convert_variant(words, n, u, dir, v);
            for (&l, w) in out.iter().zip(converted) {
                self.b.assign(l, Rvalue::Use(w));
            }
            self.b.goto(join);
            self.b.switch_to(next);
        }
        self.b.terminate(Terminator::Unreachable);
        self.b.switch_to(join);
        operands(&out)
    }

    /// Variant `v` of a value, its fields converted.
    fn convert_variant(
        &mut self,
        words: &[Operand],
        n: &Ty,
        u: &Ty,
        dir: Dir,
        v: usize,
    ) -> Vec<Operand> {
        let (nf, uf) = (self.fields_of(n, v), self.fields_of(u, v));
        let from = if dir == Dir::In { &nf } else { &uf };
        let values = (0..nf.all.len())
            .map(|j| {
                let field = self.field_words(words, from, j);
                let (outside, past) = (nf.all[j].ty.clone(), uf.all[j].ty.clone());
                self.cross_convert(field, &outside, &past, dir)
            })
            .collect();
        let to = if dir == Dir::In { u } else { n };
        self.build(to, v, values)
    }

    /// A list whose elements convert, rebuilt with each element converted.
    fn convert_list(&mut self, words: &[Operand], n: &Ty, u: &Ty, dir: Dir) -> Vec<Operand> {
        let (ne, ue) = (element_of(n), element_of(u));
        let (from, to) = sides(&ne, &ue, dir);
        let (from, to) = (from.clone(), to.clone());
        let list = word(words, 0);
        let len = self.b.define_op(
            Repr::Scalar,
            Rvalue::Runtime(Runtime::ListLen, vec![list.clone()]),
        );
        let shape = self.witness(&to);
        let out = self.b.define(
            Repr::Heap,
            Rvalue::Runtime(Runtime::ListNew, vec![len.clone(), shape]),
        );
        self.count_up(&len, |l, i| {
            let element = l.list_element(list.clone(), i, Operand::word(0), &from);
            let converted = l.cross_convert(element, &ne, &ue, dir);
            l.push_fresh(out, converted, &to);
        });
        vec![Operand::Local(out)]
    }

    /// Runs `body` for each index from 0 up to `len`.
    pub(crate) fn count_up(&mut self, len: &Operand, mut body: impl FnMut(&mut Self, Operand)) {
        let i = self.b.temp(Repr::Scalar);
        self.b.assign(i, Rvalue::Use(Operand::word(0)));
        let (head, step, exit) = (self.b.new_block(), self.b.new_block(), self.b.new_block());
        self.b.goto(head);
        self.b.switch_to(head);
        let more = self.b.define_op(
            Repr::Scalar,
            Rvalue::Prim(
                Prim::Lt(NumKind::I64),
                vec![Operand::Local(i), len.clone()],
                Operand::word(0),
            ),
        );
        self.b.branch(more, step, exit);
        self.b.switch_to(step);
        body(self, Operand::Local(i));
        let next = self.b.define_op(
            Repr::Scalar,
            Rvalue::Prim(
                Prim::Add(NumKind::I64),
                vec![Operand::Local(i), Operand::word(1)],
                Operand::word(0),
            ),
        );
        self.b.assign(i, Rvalue::Use(next));
        self.b.goto(head);
        self.b.switch_to(exit);
    }

    /// A map whose keys or values convert, rebuilt with each converted.
    fn convert_map(&mut self, words: &[Operand], n: &Ty, u: &Ty, dir: Dir) -> Vec<Operand> {
        let (from, to) = sides(n, u, dir);
        let (from, to) = (from.clone(), to.clone());
        let (fk, tk) = (key_ty(&from), key_ty(&to));
        let (fv, tv) = (map_value(&from), map_value(&to));
        let (nk, uk) = (key_ty(n), key_ty(u));
        let (nv, uv) = (map_value(n), map_value(u));
        let map = word(words, 0);
        let fresh = self.map_like(&map, (&fv, &tv), (&nv, &uv), dir, &to);
        let slot = self.copy_into_temps(vec![fresh], &to);
        self.b.make_slots(&slot);
        let pointer = self.b.define_op(Repr::Scalar, Rvalue::SlotOf(slot[0]));
        self.each_entry(&map, (&fk, &fv), |l, k, v| {
            let k = l.cross_convert(k, &nk, &uk, dir);
            let v = l.cross_convert(v, &nv, &uv, dir);
            l.map_store(&pointer, k, v, (&tk, &tv));
        });
        let out = self
            .b
            .define_op(Repr::Heap, Rvalue::Use(Operand::Local(slot[0])));
        self.b.assign(slot[0], Rvalue::Use(Operand::word(0)));
        vec![out]
    }
}

/// The value type of a map type.
pub(crate) fn map_value(map: &Ty) -> Ty {
    match map {
        Ty::Con(_, args) => args.get(1).cloned().unwrap_or(Ty::Error),
        _ => Ty::Error,
    }
}
