//! The structural impls of an array held in memory (generics.array-traits and
//! generics.large-arrays): equality, order, hashing and text, each a loop over the elements, which
//! calls the element type's impl on each in order, as the impls of an array held in words call it
//! on each of its fields.

use stilt_types::ty::Ty;

use super::Values;
use crate::lower::Lower;
use crate::lower::traits::EQUAL;
use crate::mir::{BlockId, Const, Elements, Local, Operand, Prim, Repr, Runtime, Rvalue, Stmt};
use crate::shape;

/// What a structural impl does with each element of an array held in memory: given the words
/// of the element of each value, and the element's index.
type EachPair<'f, 'a> = dyn FnMut(&mut Lower<'a>, Vec<Vec<Operand>>, Operand) + 'f;

impl<'a> Lower<'a> {
    /// The element type and the layout of an array held in memory, if `ty` is one.
    pub(super) fn in_memory_parts(&self, ty: &Ty) -> Option<(Ty, Elements<Repr>)> {
        let e = self.array_in_memory(ty)?;
        let (elem, _) = ty.arrayed()?;
        Some((elem.clone(), e))
    }

    /// Runs `body` on each element of the values, the first's and, for a binary method, the
    /// second's, borrowed, with the element's index.
    fn each_pair(
        &mut self,
        v: &Values<'_>,
        (elem, e): (&Ty, Elements<Repr>),
        binary: bool,
        body: &mut EachPair<'_, 'a>,
    ) {
        let width = e.element_words();
        let mut starts = vec![(self.in_memory(v.a.to_vec(), v.ty), width)];
        if binary {
            starts.push((self.in_memory(v.b.to_vec(), v.ty), width));
        }
        let mut each = |l: &mut Self, at: &[Operand], i: Operand| {
            let values = at.iter().map(|p| l.load_words(p, elem)).collect();
            body(l, values, i);
        };
        self.each_array_element(&starts, e.len(), &mut each);
    }

    /// Compares the elements with `eq`, going to `unequal` at the first unequal pair.
    pub(super) fn eq_elements(
        &mut self,
        v: &Values<'_>,
        parts: (Ty, Elements<Repr>),
        unequal: BlockId,
    ) {
        let (elem, e) = parts;
        let mut eq = |l: &mut Self, xy: Vec<Vec<Operand>>, _| {
            let here = l.here();
            let equal = l.trait_call("Eq", "eq", &elem, xy, here);
            let next = l.b.new_block();
            l.b.branch(equal, next, unequal);
            l.b.switch_to(next);
        };
        self.each_pair(v, (&elem.clone(), e), true, &mut eq);
    }

    /// Compares the elements lexicographically, with `compare`, into `result`.
    pub(super) fn compare_elements(
        &mut self,
        v: &Values<'_>,
        parts: (Ty, Elements<Repr>),
        (result, join): (Local, BlockId),
    ) {
        let (elem, e) = parts;
        let mut compare = |l: &mut Self, xy: Vec<Vec<Operand>>, _| {
            let here = l.here();
            let order = l.trait_call("Ord", "compare", &elem, xy, here);
            l.b.assign(result, Rvalue::Use(order.clone()));
            let same = l.b.define_op(
                Repr::Scalar,
                Rvalue::Prim(Prim::WordEq, vec![order, Operand::word(EQUAL)], l.here()),
            );
            let next = l.b.new_block();
            l.b.branch(same, next, join);
            l.b.switch_to(next);
        };
        self.each_pair(v, (&elem.clone(), e), true, &mut compare);
        self.b.assign(result, Rvalue::Use(Operand::word(EQUAL)));
        self.b.goto(join);
    }

    /// Mixes the hash of each element into `start`.
    pub(super) fn hash_elements(
        &mut self,
        v: &Values<'_>,
        parts: (Ty, Elements<Repr>),
        start: Operand,
    ) -> Operand {
        let (elem, e) = parts;
        let h = self.b.temp(Repr::Scalar);
        self.b.assign(h, Rvalue::Use(start));
        let mut hash = |l: &mut Self, x: Vec<Vec<Operand>>, _| {
            let here = l.here();
            let hx = l.trait_call("Hash", "hash", &elem, x, here);
            let mixed = Rvalue::Runtime(Runtime::HashMix, vec![Operand::Local(h), hx]);
            l.b.assign(h, mixed);
        };
        self.each_pair(v, (&elem.clone(), e), false, &mut hash);
        Operand::Local(h)
    }

    /// An array's text, as a list's: `[v, w]` (generics.array-traits), its pieces appended to a
    /// list in a loop, then joined.
    pub(super) fn show_array_elements(
        &mut self,
        v: &Values<'_>,
        parts: (Ty, Elements<Repr>),
    ) -> Operand {
        let (elem, e) = parts;
        let shape = Operand::word(shape::word(true));
        let n = Operand::word(2 * u64::from(e.len()) + 1);
        let list = self.b.define(
            Repr::Heap,
            Rvalue::Runtime(Runtime::ListNew, vec![n, shape.clone()]),
        );
        let push = |l: &mut Self, piece: Operand| {
            let args = vec![Operand::Local(list), shape.clone(), piece];
            l.b.emit(Stmt::Effect(Runtime::ListPush, args));
        };
        let text = |s: &str| Operand::Const(Const::Str(s.into()));
        push(self, text("["));
        let mut show = |l: &mut Self, x: Vec<Vec<Operand>>, i: Operand| {
            let (comma, piece) = (l.b.new_block(), l.b.new_block());
            let first = l.b.define_op(
                Repr::Scalar,
                Rvalue::Prim(Prim::WordEq, vec![i, Operand::word(0)], Operand::word(0)),
            );
            l.b.branch(first, piece, comma);
            l.b.switch_to(comma);
            push(l, text(", "));
            l.b.goto(piece);
            l.b.switch_to(piece);
            let here = l.here();
            let shown = l.trait_call("Show", "show_nested", &elem, x, here);
            push(l, shown);
        };
        self.each_pair(v, (&elem.clone(), e), false, &mut show);
        push(self, text("]"));
        self.b.define_op(
            Repr::Heap,
            Rvalue::Runtime(Runtime::Concat, vec![Operand::Local(list)]),
        )
    }
}
