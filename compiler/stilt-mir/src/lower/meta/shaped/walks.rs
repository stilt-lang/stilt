//! The walks of a shape dictionary's code over the parts of its values (traits.structural-impls):
//! each part's type is a fresh type, opened from the thunk of its descriptor with the dictionaries
//! of its table, whose impl the walk calls on the part's values, read by the part's accessor. A
//! walk calls the parts' impls in the order of the parts, and stops where the structural impls
//! compiled for a type stop (`crate::synth::structural`): `eq` at the first unequal pair, `compare`
//! at the first pair that differs.

use stilt_types::ty::Ty;

use super::Op;
use crate::described::numbered;
use crate::lower::Conv;
use crate::lower::Lower;
use crate::lower::meta::{E_GET, E_NAME, E_THUNK, E_WITNESS, FIELD_LEN, desc_ty};
use crate::lower::traits::EQUAL;
use crate::lower::words::word;
use crate::mir::{BlockId, Callee, Const, Local, NumKind, Operand, Repr, Runtime, Rvalue, Stmt};
use crate::shape;

/// Where a walk keeps what it finds from part to part: for `eq`, the block it goes to at the
/// first unequal pair; for `compare`, the order so far and the block it goes to at the first
/// pair that differs; for `hash`, the hash so far; for `show`, the list of the text's pieces.
pub(super) struct Acc {
    pub(super) op: Op,
    pub(super) result: Local,
    pub(super) exit: BlockId,
}

/// A value's type and its words, each value in one word.
pub(super) type Values<'v> = (&'v Ty, &'v [Operand]);

impl<'a> Lower<'a> {
    /// The walk of a tuple's or a record's fields, by the descriptor's count and entries, with
    /// `Show`'s opening, closing and whether its fields are written with their names.
    pub(super) fn walk_fields(
        &mut self,
        op: Op,
        fields: &(Operand, Operand),
        values: Values<'_>,
        frame: Option<(Operand, Operand, Operand)>,
    ) -> Operand {
        let (ends, labeled) = match frame {
            Some((open, close, labeled)) => (Some((open, close)), Some(labeled)),
            None => (None, None),
        };
        self.framed(op, ends, &mut |l, acc| {
            l.fields_into(acc, fields, values, labeled.as_ref());
        })
    }

    /// The walk of an array's elements, which its closure `get` gives as a list, of its size.
    pub(super) fn walk_array(
        &mut self,
        op: Op,
        (thunk, size, get): (Operand, Operand, Operand),
        (ty, values): Values<'_>,
    ) -> Operand {
        let mark = self.generics.len();
        let elem = self.fresh_type(thunk, None);
        let list = Ty::list(elem.clone());
        let lists: Vec<Operand> = values
            .iter()
            .map(|v| {
                let arg = self.lend(vec![v.clone()], ty);
                let (ret, err) = (Conv::boxed(list.clone()), Conv::boxed(Ty::Error));
                let callee = Callee::Value(get.clone());
                let loc = Operand::Local(self.loc);
                word(
                    &self.finish_call(callee, vec![arg], &[], loc, false, &ret, &err),
                    0,
                )
            })
            .collect();
        let text = |s: &str| Operand::Const(Const::Str(s.into()));
        let ends = (op == Op::Show).then(|| (text("["), text("]")));
        let value = self.framed(op, ends, &mut |l, acc| {
            l.each_part(size.clone(), &mut |l, i| {
                let loc = Operand::Local(l.loc);
                let xs = lists
                    .iter()
                    .map(|x| l.list_element(x.clone(), i.clone(), loc.clone(), &elem))
                    .collect();
                l.part(acc, &elem, xs, i, None);
            });
        });
        self.close_fresh(mark);
        value
    }

    /// What a walk gives, around the loop over the parts that `parts` writes: for `eq`, true
    /// unless a pair is unequal; for `compare`, the first order that isn't `Equal`, or
    /// `Equal`; for `hash`, the parts' hashes mixed in order into a new hash; for `show`, the
    /// pieces between `ends`, concatenated.
    pub(super) fn framed(
        &mut self,
        op: Op,
        ends: Option<(Operand, Operand)>,
        parts: &mut dyn FnMut(&mut Lower<'a>, &Acc),
    ) -> Operand {
        let result = self.b.temp(if op == Op::Show {
            Repr::Heap
        } else {
            Repr::Scalar
        });
        let join = self.b.new_block();
        let exit = if op == Op::Eq {
            self.b.new_block()
        } else {
            join
        };
        match op {
            Op::Hash => {
                let start = hash_start(self);
                self.b.assign(result, Rvalue::Use(start));
            }
            Op::Show => {
                let shape = Operand::word(shape::word(true));
                let new = Rvalue::Runtime(Runtime::ListNew, vec![Operand::word(4), shape]);
                self.b.assign(result, new);
            }
            Op::Eq | Op::Compare => {}
        }
        let (open, close) = ends.unzip();
        if let Some(open) = open {
            self.push_piece(result, open);
        }
        parts(self, &Acc { op, result, exit });
        match op {
            Op::Eq => self.b.assign(result, Rvalue::Use(Operand::word(1))),
            Op::Compare => self.b.assign(result, Rvalue::Use(Operand::word(EQUAL))),
            Op::Hash => {}
            Op::Show => {
                if let Some(close) = close {
                    self.push_piece(result, close);
                }
                let text = Rvalue::Runtime(Runtime::Concat, vec![Operand::Local(result)]);
                let text = self.b.define_op(Repr::Heap, text);
                self.b.goto(join);
                self.b.switch_to(join);
                return text;
            }
        }
        self.b.goto(join);
        if op == Op::Eq {
            self.b.switch_to(exit);
            self.b.assign(result, Rvalue::Use(Operand::word(0)));
            self.b.goto(join);
        }
        self.b.switch_to(join);
        Operand::Local(result)
    }

    /// The parts of values by a descriptor's count and entries of fields, each part's type
    /// opened from its entry, and its values read by its accessor.
    pub(super) fn fields_into(
        &mut self,
        acc: &Acc,
        (count, entries): &(Operand, Operand),
        (ty, values): Values<'_>,
        labeled: Option<&Operand>,
    ) {
        let loc = Operand::Local(self.loc);
        self.each_part(count.clone(), &mut |l, i| {
            let entry = l.list_element(entries.clone(), i.clone(), loc.clone(), &desc_ty());
            let entry = word(&entry, 0);
            let mark = l.generics.len();
            let thunk = l.read(entry.clone(), FIELD_LEN, E_THUNK, Repr::Heap);
            let witness = l.read(entry.clone(), FIELD_LEN, E_WITNESS, Repr::Scalar);
            let part = l.fresh_type(thunk, Some(witness));
            let xs = values
                .iter()
                .map(|v| {
                    let given = [(vec![v.clone()], ty.clone())];
                    l.call_field(
                        entry.clone(),
                        (FIELD_LEN, E_GET),
                        &given,
                        &part,
                        loc.clone(),
                    )
                })
                .collect();
            let label = labeled.map(|flag| (flag.clone(), entry));
            l.part(acc, &part, xs, i, label);
            l.close_fresh(mark);
        });
    }

    /// What a walk does with the values of one part, of type `part`, the `i`th: for `show`,
    /// after a separator from the part before, and its field's name where `label` holds.
    fn part(
        &mut self,
        acc: &Acc,
        part: &Ty,
        xs: Vec<Vec<Operand>>,
        i: Operand,
        label: Option<(Operand, Operand)>,
    ) {
        let loc = Operand::Local(self.loc);
        match acc.op {
            Op::Eq => {
                let equal = self.trait_call("Eq", "eq", part, xs, loc);
                let next = self.b.new_block();
                self.b.branch(equal, next, acc.exit);
                self.b.switch_to(next);
            }
            Op::Compare => {
                let order = self.trait_call("Ord", "compare", part, xs, loc);
                self.b.assign(acc.result, Rvalue::Use(order.clone()));
                let same = self.word_eq(order, Operand::word(EQUAL));
                let next = self.b.new_block();
                self.b.branch(same, next, acc.exit);
                self.b.switch_to(next);
            }
            Op::Hash => {
                let h = self.trait_call("Hash", "hash", part, xs, loc);
                let mixed = Rvalue::Runtime(Runtime::HashMix, vec![Operand::Local(acc.result), h]);
                self.b.assign(acc.result, mixed);
            }
            Op::Show => {
                let first = self.word_eq(i, Operand::word(0));
                self.unless(first, |l| {
                    l.push_piece(acc.result, Operand::Const(Const::Str(", ".into())));
                });
                if let Some((flag, entry)) = label {
                    let plain = self.word_eq(flag, Operand::word(0));
                    self.unless(plain, |l| {
                        let name = l.read(entry, FIELD_LEN, E_NAME, Repr::Heap);
                        let colon = Operand::Const(Const::Str(": ".into()));
                        let named = Rvalue::Runtime(Runtime::Concat2, vec![name, colon]);
                        let named = l.b.define_op(Repr::Heap, named);
                        l.push_piece(acc.result, named);
                    });
                }
                let text = self.trait_call("Show", "show_nested", part, xs, loc);
                self.push_piece(acc.result, text);
            }
        }
    }

    /// Runs `body` on each index from 0 to `count`, in order.
    pub(super) fn each_part(
        &mut self,
        count: Operand,
        body: &mut dyn FnMut(&mut Lower<'a>, Operand),
    ) {
        let i = self.b.temp(Repr::Scalar);
        self.b.assign(i, Rvalue::Use(Operand::word(0)));
        let (head, each, next, exit) = self.loop_blocks();
        self.b.goto(head);
        self.b.switch_to(head);
        let more = self.lt(NumKind::I64, Operand::Local(i), count);
        self.b.branch(more, each, exit);
        self.b.switch_to(each);
        body(self, Operand::Local(i));
        self.b.goto(next);
        self.b.switch_to(next);
        self.step(i);
        self.b.goto(head);
        self.b.switch_to(exit);
    }

    /// Runs `then` where `cond` doesn't hold.
    fn unless(&mut self, cond: Operand, then: impl FnOnce(&mut Self)) {
        let (yes, after) = (self.b.new_block(), self.b.new_block());
        self.b.branch(cond, after, yes);
        self.b.switch_to(yes);
        then(self);
        self.b.goto(after);
        self.b.switch_to(after);
    }

    fn push_piece(&mut self, list: Local, piece: Operand) {
        let shape = Operand::word(shape::word(true));
        let push = Stmt::Effect(Runtime::ListPush, vec![Operand::Local(list), shape, piece]);
        self.b.emit(push);
    }

    /// A fresh type of the walk, opened from the thunk of its descriptor: a part's type.
    pub(super) fn fresh_type(&mut self, thunk: Operand, witness: Option<Operand>) -> Ty {
        let n = u32::try_from(self.generics.len()).expect("under 4G generics");
        let g = numbered(1 << 30 | n);
        self.open_fresh(&g, thunk, witness);
        Ty::Param(g)
    }
}

/// A new hash, before any part is mixed in.
pub(super) fn hash_start(l: &mut Lower<'_>) -> Operand {
    l.b.define_op(
        Repr::Scalar,
        Rvalue::Runtime(Runtime::HashStart, Vec::new()),
    )
}
