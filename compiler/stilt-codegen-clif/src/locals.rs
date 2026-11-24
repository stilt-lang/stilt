//! Where a function's locals live: each in a Cranelift variable of its type, `F64` for a local
//! that holds an `f64` and `I64` for every other, or in a stack slot when a pointer to it is
//! taken. The locals that hold the words of one value share a slot, one word after the other,
//! so that a pointer to the first reaches them all. A value given to a local of the other type
//! is converted by a bitcast, which keeps its bits ([`crate::floats`]).
//!
//! An array held in memory (generics.large-arrays; `stilt_mir::mir::Repr::Array`) lives in a slot
//! too, or among its group's words, and its operand is the address of its words
//! ([`crate::arrays`]).
//!
//! A function with more than [`MOST_VARIABLES`] locals keeps every local in memory, one word
//! after the other: Cranelift numbers a block's parameters, which its variables become where
//! control flow joins, in 16 bits.

use cranelift_codegen::ir::immediates::Ieee64;
use cranelift_codegen::ir::types::{F64, I64};
use cranelift_codegen::ir::{
    InstBuilder, StackSlot, StackSlotData, StackSlotKind, Type, Value, ValueLabel,
};
use stilt_mir::mir::{Local, Repr, offsets};

use crate::translate::Translator;

/// The most locals that a function keeps in Cranelift's variables.
const MOST_VARIABLES: usize = 8192;

impl Translator<'_, '_> {
    /// Gives every local a variable or a slot, holding 0 until it is assigned, so that a drop
    /// of a local not yet assigned releases nothing. An array held in memory has a slot of its
    /// own, or its words in its group's, and is cleared only if it holds counted words, which a
    /// drop would read.
    pub(crate) fn declare_locals(&mut self) -> Result<(), String> {
        let zero = self.fb.ins().iconst(I64, 0);
        let float_zero = self.fb.ins().f64const(Ieee64::with_bits(0));
        if self.f.locals.len() > MOST_VARIABLES {
            return self.locals_in_memory(zero);
        }
        let locals = &self.f.locals;
        let mut groups = Vec::new();
        for (i, decl) in locals.iter().enumerate() {
            let ty = self.types[i];
            let var = self.fb.declare_var(ty);
            self.fb
                .def_var(var, if ty == F64 { float_zero } else { zero });
            self.vars.push(var);
            let array = matches!(decl.repr, Repr::Array(_));
            if (!decl.slot && !array) || (decl.slot && decl.grouped) {
                continue;
            }
            let n = if decl.slot {
                1 + locals[i + 1..]
                    .iter()
                    .take_while(|d| d.slot && d.grouped)
                    .count()
            } else {
                1
            };
            groups.push(i..i + n);
        }
        for group in groups {
            let words = offsets(group.clone().map(|i| self.f.locals[i].repr)).1;
            let slot = self.words_slot(words);
            self.place(group, slot, zero)?;
        }
        Ok(())
    }

    /// Gives every local a word of one slot, holding 0, the words of one value in memory one
    /// after the other, as their grouped slots are, and an array held in memory its words.
    fn locals_in_memory(&mut self, zero: Value) -> Result<(), String> {
        let n = self.f.locals.len();
        for i in 0..n {
            let var = self.fb.declare_var(self.types[i]);
            self.vars.push(var);
        }
        let words = offsets(self.f.locals.iter().map(|d| d.repr)).1;
        let slot = self.words_slot(words);
        self.place(0..n, slot, zero)
    }

    /// Puts the locals of `group` in `slot`, one after the other, each holding 0.
    fn place(
        &mut self,
        group: std::ops::Range<usize>,
        slot: StackSlot,
        zero: Value,
    ) -> Result<(), String> {
        let mut at = 0;
        for i in group {
            let offset = i32::try_from(8 * at).expect("a slot under 2 GiB");
            let repr = self.f.locals[i].repr;
            match repr {
                Repr::Array(e) if e.counted() => {
                    let addr = self.fb.ins().stack_addr(I64, slot, offset);
                    self.zero_words(addr, e.words())?;
                }
                Repr::Array(_) => {}
                _ => {
                    self.fb.ins().stack_store(I64, zero, slot, offset);
                }
            }
            let local = Local(u32::try_from(i).expect("under 4G locals"));
            self.slots.insert(local, (slot, offset));
            at += repr.words();
        }
        Ok(())
    }

    /// A stack slot for `words` words. Each slot takes a multiple of 16 bytes, aligned to 16,
    /// because Cranelift's spill slots follow them and a float register spills as 16 bytes: a
    /// spill only 8-aligned crosses a cache line in a quarter of the frames, and then each of
    /// its reloads in a loop waits for the store, which can't be forwarded (goal debug-speed).
    pub(crate) fn words_slot(&mut self, words: usize) -> StackSlot {
        let size = u32::try_from(8 * words.next_multiple_of(2)).expect("a slot under 4 GiB");
        self.fb
            .create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size, 4))
    }

    /// The type of a local's values.
    pub(crate) fn local_type(&self, l: Local) -> Type {
        self.types[l.0 as usize]
    }

    /// A local's value, of its type: for an array held in memory, the address of its words.
    pub(crate) fn use_local(&mut self, l: Local) -> Value {
        if self.array_of(l).is_some() {
            return self.slot_addr(l);
        }
        let ty = self.local_type(l);
        match self.slots.get(&l) {
            Some(&(slot, offset)) => self.fb.ins().stack_load(I64, ty, slot, offset),
            None => self.fb.use_var(self.vars[l.0 as usize]),
        }
    }

    /// Gives a local the value `v`, converted to its type: an array held in memory the words
    /// that `v` points to, copied.
    pub(crate) fn def_local(&mut self, l: Local, v: Value) -> Result<(), String> {
        if let Some(e) = self.array_of(l) {
            let to = self.slot_addr(l);
            return self.copy_words(to, v, e.words());
        }
        let v = self.converted(v, self.local_type(l));
        if self.f.locals[l.0 as usize].shown.is_some() {
            self.labels.push((v, ValueLabel::from_u32(l.0)));
        }
        match self.slots.get(&l) {
            Some(&(slot, offset)) => {
                self.fb.ins().stack_store(I64, v, slot, offset);
            }
            None => self.fb.def_var(self.vars[l.0 as usize], v),
        }
        Ok(())
    }

    pub(crate) fn slot_addr(&mut self, l: Local) -> Value {
        let (slot, offset) = self.slots[&l];
        self.fb.ins().stack_addr(I64, slot, offset)
    }

    pub(crate) fn repr(&self, l: Local) -> Repr {
        self.f.locals[l.0 as usize].repr
    }
}
