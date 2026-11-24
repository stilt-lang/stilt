//! The walk of a variant type's values (traits.structural-impls): the variant each is, found by the
//! variants' accessors in the order of their declaration, then the fields of the tuple of its
//! payload, as `super::walks` walks a tuple's. Values of different variants are unequal
//! without a payload compared, and ordered by their variants' order; a value's hash mixes in
//! its variant's index first, and its text is its variant's name, then its payload's fields in
//! parentheses, as the impls compiled for a variant type give them.

use stilt_types::ty::Ty;

use super::Op;
use super::walks::{Acc, Values, hash_start};
use crate::lower::meta::{
    A, B, CASE_LEN, DESC_LEN, E_GET, E_INDEX, E_NAME, E_THUNK, E_WITNESS, desc_ty,
};
use crate::lower::traits::{EQUAL, GREATER, LESS};
use crate::lower::words::word;
use crate::lower::{Generic, Lower};
use crate::mir::{BlockId, Const, Local, Operand, Prim, Repr, Runtime, Rvalue};

impl Lower<'_> {
    /// The walk of a variant type's values: the variant each is, by the variants' accessors in
    /// the order of their declaration, then the fields of the tuple of its payload. Values of
    /// different variants are unequal, and ordered by their variants' order.
    pub(super) fn walk_variants(
        &mut self,
        op: Op,
        (count, entries): (Operand, Operand),
        (ty, values): Values<'_>,
    ) -> Operand {
        let result = self.b.temp(if op == Op::Show {
            Repr::Heap
        } else {
            Repr::Scalar
        });
        let join = self.b.new_block();
        let unequal = (op == Op::Eq).then(|| self.b.new_block());
        let loc = Operand::Local(self.loc);
        self.each_part(count, &mut |l, i| {
            let entry = l.list_element(entries.clone(), i, loc.clone(), &desc_ty());
            let entry = word(&entry, 0);
            let mark = l.generics.len();
            let thunk = l.read(entry.clone(), CASE_LEN, E_THUNK, Repr::Heap);
            let witness = l.read(entry.clone(), CASE_LEN, E_WITNESS, Repr::Scalar);
            let payload = l.fresh_type(thunk, Some(witness));
            let found: Vec<(Operand, Operand)> = values
                .iter()
                .map(|v| l.case_payload(entry.clone(), (ty, v.clone()), &payload))
                .collect();
            let acc = Acc {
                op,
                result,
                exit: unequal.unwrap_or(join),
            };
            l.variant_case(&acc, (&entry, &payload), &found, join);
            l.close_fresh(mark);
        });
        // Every value is one of its variants, so no value reaches the end of the loop.
        let last = match op {
            Op::Eq => Operand::word(1),
            Op::Compare => Operand::word(EQUAL),
            Op::Hash => hash_start(self),
            Op::Show => Operand::Const(Const::Str("".into())),
        };
        self.b.assign(result, Rvalue::Use(last));
        self.b.goto(join);
        if let Some(unequal) = unequal {
            self.b.switch_to(unequal);
            self.b.assign(result, Rvalue::Use(Operand::word(0)));
            self.b.goto(join);
        }
        self.b.switch_to(join);
        Operand::Local(result)
    }

    /// The code of one variant: given whether each value is that variant, with its payload,
    /// it goes on to the next variant unless the first value is this one, or for `compare`,
    /// either is: a first value of this variant and a second of a later one is `Less`, and the
    /// other way round `Greater`.
    fn variant_case(
        &mut self,
        acc: &Acc,
        (entry, payload): (&Operand, &Ty),
        found: &[(Operand, Operand)],
        join: BlockId,
    ) {
        let (is_a, pa) = found[0].clone();
        let pair = found.get(1).cloned();
        let (this, next) = (self.b.new_block(), self.b.new_block());
        let either = match (acc.op, &pair) {
            (Op::Compare, Some((is_b, _))) => self.either(is_a.clone(), is_b.clone()),
            _ => is_a.clone(),
        };
        self.b.branch(either, this, next);
        self.b.switch_to(this);
        let mut words = vec![pa];
        if let Some((is_b, pb)) = pair {
            words.push(pb);
            let both = self.b.new_block();
            if acc.op == Op::Compare {
                let all = self.both(is_a.clone(), is_b);
                let one = self.b.new_block();
                self.b.branch(all, both, one);
                self.b.switch_to(one);
                self.ordered_apart(acc.result, is_a, join);
            } else {
                self.b.branch(is_b, both, acc.exit);
            }
            self.b.switch_to(both);
        }
        let desc = self.generic(payload).and_then(|g: &Generic| g.desc.clone());
        let desc = desc.unwrap_or(Operand::word(0));
        let count = self.read(desc.clone(), DESC_LEN, A, Repr::Scalar);
        let entries = self.read(desc, DESC_LEN, B, Repr::Heap);
        let fields = (count.clone(), entries.clone());
        match acc.op {
            Op::Eq | Op::Compare => {
                self.fields_into(acc, &fields, (payload, &words), None);
                let same = if acc.op == Op::Eq { 1 } else { EQUAL };
                self.b.assign(acc.result, Rvalue::Use(Operand::word(same)));
            }
            Op::Hash => {
                let index = self.read(entry.clone(), CASE_LEN, E_INDEX, Repr::Scalar);
                let start = hash_start(self);
                let mixed = Rvalue::Runtime(Runtime::HashMix, vec![start, index]);
                self.b.assign(acc.result, mixed);
                self.fields_into(acc, &fields, (payload, &words), None);
            }
            Op::Show => self.show_variant(acc, (entry, payload), (count, entries), &words, join),
        }
        self.b.goto(join);
        self.b.switch_to(next);
    }

    /// For `compare`, where only one of the values is this variant: `Less` when it is the
    /// first, whose variant comes before the second's, and otherwise `Greater`.
    fn ordered_apart(&mut self, result: Local, is_a: Operand, join: BlockId) {
        let (less, greater) = (self.b.new_block(), self.b.new_block());
        self.b.branch(is_a, less, greater);
        for (block, order) in [(less, LESS), (greater, GREATER)] {
            self.b.switch_to(block);
            self.b.assign(result, Rvalue::Use(Operand::word(order)));
            self.b.goto(join);
        }
    }

    /// The text of a variant: its name alone without a payload, and otherwise its name, then
    /// the payload's fields in parentheses (std.show-output).
    fn show_variant(
        &mut self,
        acc: &Acc,
        (entry, payload): (&Operand, &Ty),
        (count, entries): (Operand, Operand),
        words: &[Operand],
        join: BlockId,
    ) {
        let name = self.read(entry.clone(), CASE_LEN, E_NAME, Repr::Heap);
        let (bare, full) = (self.b.new_block(), self.b.new_block());
        let none = self.word_eq(count.clone(), Operand::word(0));
        self.b.branch(none, bare, full);
        self.b.switch_to(bare);
        self.b.assign(acc.result, Rvalue::Use(name.clone()));
        self.b.goto(join);
        self.b.switch_to(full);
        let open = Operand::Const(Const::Str("(".into()));
        let head = self.b.define_op(
            Repr::Heap,
            Rvalue::Runtime(Runtime::Concat2, vec![name, open]),
        );
        let close = Operand::Const(Const::Str(")".into()));
        let fields = (count, entries);
        let text = self.framed(Op::Show, Some((head, close)), &mut |l, inner| {
            l.fields_into(inner, &fields, (payload, words), None);
        });
        self.b.assign(acc.result, Rvalue::Use(text));
    }

    /// Whether a value of type `ty` is the variant whose entry is `entry`, and its payload, of
    /// the type `payload`, in one word: by the variant's accessor, which gives an option.
    fn case_payload(
        &mut self,
        entry: Operand,
        (ty, v): (&Ty, Operand),
        payload: &Ty,
    ) -> (Operand, Operand) {
        let option = Ty::option(payload.clone());
        let loc = Operand::Local(self.loc);
        let given = [(vec![v], ty.clone())];
        let got = self.call_field(entry, (CASE_LEN, E_GET), &given, &option, loc);
        let is = self.is_variant(&got, &option, 1);
        let fields = self.fields_of(&option, 1);
        let words = self.field_words(&got, &fields, 0);
        (is, word(&words, 0))
    }

    fn either(&mut self, a: Operand, b: Operand) -> Operand {
        let or = Rvalue::Prim(Prim::BitOr, vec![a, b], Operand::word(0));
        self.b.define_op(Repr::Scalar, or)
    }
}
