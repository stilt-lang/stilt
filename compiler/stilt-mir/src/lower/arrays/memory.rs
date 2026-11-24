//! Arrays held in memory (generics.large-arrays and generics.array-effects): one local of the frame
//! ([`Repr::Array`]) holds the words of all the elements, which code makes, reads and visits
//! through a pointer to them, in a loop over the elements wherever it would otherwise name each
//! one, so that the code is the same whatever the array's size. The frame's memory is no
//! allocation, so none of this adds `alloc`.

use stilt_types::ty::Ty;

use crate::lower::Lower;
use crate::lower::words::Fields;
use crate::mir::{Elements, Local, NumKind, Operand, Repr, Rvalue};

impl Lower<'_> {
    /// A new local in memory for an array of the layout `e`, which holds nothing until code
    /// stores its elements, and a pointer to its words.
    pub(crate) fn new_array(&mut self, e: Elements<Repr>) -> (Local, Operand) {
        let array = self.b.temp(Repr::Array(e));
        self.b.make_slots(&[array]);
        let pointer = self.b.define_op(Repr::Scalar, Rvalue::SlotOf(array));
        (array, pointer)
    }

    /// A pointer to a copy, in memory, of a word of the representation `repr`.
    pub(crate) fn word_in_memory(&mut self, w: Operand, repr: Repr) -> Operand {
        let copy = self.b.define(repr, Rvalue::Use(w));
        self.b.make_slots(&[copy]);
        self.b.define_op(Repr::Scalar, Rvalue::SlotOf(copy))
    }

    /// An array in memory of the layout `e`, of the values of its elements, each with its type,
    /// which it consumes.
    pub(crate) fn array_of(
        &mut self,
        e: Elements<Repr>,
        values: Vec<(Vec<Operand>, Ty)>,
    ) -> Vec<Operand> {
        let (array, pointer) = self.new_array(e);
        let width = e.element_words();
        for (i, (words, ty)) in values.into_iter().enumerate() {
            let at = self.offset(pointer.clone(), i * width);
            self.store_words(&at, words, &ty);
        }
        vec![Operand::Local(array)]
    }

    /// Runs `body` once for each element of arrays of `len` elements, whose words start where
    /// `starts` point, each with its elements' width in words, in order, with the pointers to
    /// the elements and the element's index. The body ends in the block that goes on to the
    /// next element.
    pub(crate) fn each_array_element(
        &mut self,
        starts: &[(Operand, usize)],
        len: u32,
        body: &mut dyn FnMut(&mut Self, &[Operand], Operand),
    ) {
        let index = self.b.temp(Repr::Scalar);
        self.b.assign(index, Rvalue::Use(Operand::word(0)));
        let (head, each, exit) = (self.b.new_block(), self.b.new_block(), self.b.new_block());
        self.b.goto(head);
        self.b.switch_to(head);
        let more = self.lt(
            NumKind::I64,
            Operand::Local(index),
            Operand::word(u64::from(len)),
        );
        self.b.branch(more, each, exit);
        self.b.switch_to(each);
        let at: Vec<Operand> = starts
            .iter()
            .map(|(s, width)| self.array_element_at(s.clone(), Operand::Local(index), *width))
            .collect();
        body(self, &at, Operand::Local(index));
        self.step(index);
        self.b.goto(head);
        self.b.switch_to(exit);
    }

    /// An array in memory of the layout `e`, each element the words of `x`, which it consumes,
    /// for `array.fill` (generics.arrays).
    pub(crate) fn filled(&mut self, e: Elements<Repr>, x: &[Operand], elem: &Ty) -> Vec<Operand> {
        let (array, pointer) = self.new_array(e);
        let mut store = |l: &mut Self, at: &[Operand], _| l.store_words(&at[0], x.to_vec(), elem);
        self.each_array_element(&[(pointer, e.element_words())], e.len(), &mut store);
        vec![Operand::Local(array)]
    }

    /// A new list of the elements of an array of type `ty` held in memory, whose words are `v`,
    /// of the element type `elem` and the layout `e`.
    pub(crate) fn list_of_array(
        &mut self,
        v: &[Operand],
        ty: &Ty,
        (elem, e): (&Ty, Elements<Repr>),
    ) -> Operand {
        let shape = self.witness(elem);
        let n = Operand::word(u64::from(e.len()));
        let list = self.b.define(
            Repr::Heap,
            Rvalue::Runtime(crate::mir::Runtime::ListNew, vec![n, shape]),
        );
        let pointer = self.in_memory(v.to_vec(), ty);
        let mut push = |l: &mut Self, at: &[Operand], _| {
            let x = l.load_words(&at[0], elem);
            l.push_fresh(list, x, elem);
        };
        self.each_array_element(&[(pointer, e.element_words())], e.len(), &mut push);
        Operand::Local(list)
    }

    /// The words of elements `0..n` of an array of type `ty` whose words are `v`, borrowed: a
    /// field each of an array held in words, and of one held in memory, the words a pointer to
    /// a copy of it reaches.
    pub(crate) fn elements_of(&mut self, v: &[Operand], ty: &Ty, n: usize) -> Vec<Vec<Operand>> {
        let Some((elem, _)) = ty.arrayed() else {
            return Vec::new();
        };
        if self.array_in_memory(ty).is_none() {
            let fields: Fields = self.fields_of(ty, 0);
            return (0..n).map(|j| self.field_words(v, &fields, j)).collect();
        }
        let elem = elem.clone();
        let width = self.words_of(&elem);
        let pointer = self.in_memory(v.to_vec(), ty);
        (0..n)
            .map(|j| {
                let at = self.offset(pointer.clone(), j * width);
                self.load_words(&at, &elem)
            })
            .collect()
    }
}
