//! Translating rvalues: data objects, fields, tags, slots and constants. A word read from
//! memory is loaded as a value of the type of the local it goes to, a float for one that holds
//! an `f64` ([`crate::floats`]).

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{
    InstBuilder, Type, Value,
    types::{I16, I64},
};
use stilt_mir::FnRef;
use stilt_mir::mir::{Heapness, Local, Operand, Repr, Runtime, Rvalue, offsets};

use stilt_runtime::layout;

use crate::arrays::as_i64;
use crate::lists::constant;
use crate::module::{HEADER, in_memory, signature};
use crate::translate::Translator;

/// The number of words of a data object of these fields.
fn data_words(fields: &[(Operand, Heapness)]) -> usize {
    fields.iter().map(|(_, h)| h.words()).sum()
}

/// The constant word of an operand that the MIR gives as one.
fn word_of(o: &Operand) -> Result<u64, String> {
    constant(o).ok_or_else(|| format!("a constant operand, not {o:?}"))
}

impl Translator<'_, '_> {
    /// The value of `r`, which goes to the local `dest`.
    pub(crate) fn rvalue(&mut self, r: &Rvalue, dest: Local) -> Result<Value, String> {
        let ty = self.local_type(dest);
        match r {
            Rvalue::Use(o) => self.typed_operand(o, ty),
            Rvalue::Prim(p, args, loc) => self.prim(*p, args, loc),
            Rvalue::Alloc(tag, fields) => self.alloc(*tag, fields),
            Rvalue::AllocIn(memory, tag, fields, _) => self.alloc_in(memory, *tag, fields),
            Rvalue::Field { base, index, .. } => {
                let b = self.operand(base)?;
                let addr = self.field_addr(b, *index);
                Ok(self.fb.ins().load(ty, self.trusted, addr, 0))
            }
            Rvalue::Tag(o) => {
                let v = self.operand(o)?;
                Ok(self.tag(v))
            }
            Rvalue::Load(o) => {
                let p = self.operand(o)?;
                Ok(self.fb.ins().load(ty, self.trusted, p, 0))
            }
            Rvalue::SlotOf(l) => Ok(self.slot_addr(*l)),
            Rvalue::Offset(o, words) => {
                let p = self.operand(o)?;
                Ok(self.fb.ins().iadd_imm_s(p, 8 * i64::from(*words)))
            }
            Rvalue::FieldSlot { slot, index, .. } => {
                let s = self.operand(slot)?;
                let object = self.unique(s)?;
                Ok(self.field_addr(object, *index))
            }
            Rvalue::Runtime(f, args) => self.runtime_value(*f, args, ty),
            Rvalue::Constant(f, loc, k, words, _) => self.constant(f, loc, (*k, words), ty),
        }
    }

    /// The result of a runtime function, as a value of type `ty`, computed inline where the
    /// function has a fast path.
    fn runtime_value(&mut self, f: Runtime, args: &[Operand], ty: Type) -> Result<Value, String> {
        // The location of an index is only read when the index is out of bounds, and the shape
        // of a list's elements is a constant where the code names their type.
        match (f, args) {
            (Runtime::ListIndex, [loc, list, i, elem, word]) => {
                let (list, i) = (self.operand(list)?, self.operand(i)?);
                return self.list_index(loc, list, i, (word_of(elem)?, word_of(word)?), ty);
            }
            (Runtime::ListAt, [list, i, elem, word]) => {
                let (list, i) = (self.operand(list)?, self.operand(i)?);
                return Ok(self.list_at(list, i, word_of(elem)?, word_of(word)?, ty));
            }
            (Runtime::ListSlot, [loc, slot, i, elem]) => {
                let (slot, i) = (self.operand(slot)?, self.operand(i)?);
                return self.list_slot(loc, slot, i, word_of(elem)?);
            }
            (Runtime::ListSlotAt, [slot, i, elem]) => {
                let (slot, i) = (self.operand(slot)?, self.operand(i)?);
                return self.list_slot_at(slot, i, word_of(elem)?);
            }
            (Runtime::ListElement, [loc, slot, i, elem]) => {
                let (slot, i) = (self.operand(slot)?, self.operand(i)?);
                return self.list_element(loc, slot, i, word_of(elem)?);
            }
            (Runtime::ListElementAt, [slot, i, elem]) => {
                let (slot, i) = (self.operand(slot)?, self.operand(i)?);
                return Ok(self.list_element_at(slot, i, word_of(elem)?));
            }
            (Runtime::ListGet, [loc, list, i, shape]) => {
                let (list, i, shape) =
                    (self.operand(list)?, self.operand(i)?, self.operand(shape)?);
                return self.list_get(loc, list, i, shape);
            }
            (Runtime::Shape, words) => return self.shape_of(words),
            (Runtime::ShapeParts, parts) => return self.shape_parts(parts),
            // The map is an operand only so that it lives as long as the word.
            (Runtime::MapWord, [_, pointer, i]) => {
                let p = self.operand(pointer)?;
                let at = i32::try_from(8 * word_of(i)?).map_err(|e| e.to_string())?;
                return Ok(self.fb.ins().load(ty, self.trusted, p, at));
            }
            _ => {}
        }
        let values = args
            .iter()
            .map(|a| self.operand(a))
            .collect::<Result<Vec<_>, _>>()?;
        match (f, values.as_slice()) {
            (Runtime::ListLen, &[list]) => Ok(self.list_len(list)),
            (Runtime::Unique, &[slot]) => self.unique(slot),
            _ => match self.runtime(f.symbol(), &values, f.returns())? {
                Some(v) => Ok(v),
                None => Ok(self.fb.ins().iconst(I64, 0)),
            },
        }
    }

    /// A runtime function called for its effect, inline where it has a fast path.
    pub(crate) fn effect(&mut self, f: Runtime, args: &[Operand]) -> Result<(), String> {
        match (f, args) {
            (Runtime::ListPush, _) => return self.list_push(args),
            (Runtime::ListAppend, _) => return self.list_append(args),
            (Runtime::StorePacked, _) => return self.store_packed(args),
            (Runtime::Unique, [slot]) => {
                let slot = self.operand(slot)?;
                return self.unique(slot).map(|_| ());
            }
            _ => {}
        }
        let values = args
            .iter()
            .map(|a| self.operand(a))
            .collect::<Result<Vec<_>, _>>()?;
        self.runtime(f.symbol(), &values, f.returns())?;
        Ok(())
    }

    /// A new data object, its fields and its layout set.
    fn alloc(&mut self, tag: u16, fields: &[(Operand, Heapness)]) -> Result<Value, String> {
        let len = data_words(fields);
        let n = self.fb.ins().iconst(I64, as_i64(len)?);
        let t = self.fb.ins().iconst(I64, i64::from(tag));
        let object = self
            .runtime("stilt_rt_alloc_data", &[n, t], true)?
            .expect("a result");
        self.fill_data(object, fields)?;
        Ok(object)
    }

    /// [`Self::alloc`], in the memory that `memory` holds when it isn't 0, which the runtime
    /// makes a new object's, of no heap words until its layout is set.
    fn alloc_in(
        &mut self,
        memory: &Operand,
        tag: u16,
        fields: &[(Operand, Heapness)],
    ) -> Result<Value, String> {
        let memory = self.operand(memory)?;
        let n = self.fb.ins().iconst(I64, as_i64(data_words(fields))?);
        let t = self.fb.ins().iconst(I64, i64::from(tag));
        let object = self
            .runtime("stilt_rt_renew", &[memory, n, t], true)?
            .expect("a result");
        self.fill_data(object, fields)?;
        Ok(object)
    }

    /// A box of the words `fields` on the stack, lent for a call: its header has a count of 0,
    /// which no count changes or frees, and the tag of a box (`stilt_runtime::abi`).
    pub(crate) fn lent(&mut self, fields: &[(Operand, Heapness)]) -> Result<Value, String> {
        let len = data_words(fields);
        let slot = self.words_slot(HEADER as usize / 8 + len + layout::mask_words(len));
        let object = self.fb.ins().stack_addr(I64, slot, 0);
        let kind_and_tag = i64::from(stilt_mir::mir::BOX) << 48;
        let first = self.fb.ins().iconst(I64, kind_and_tag);
        self.fb.ins().store(self.trusted, first, object, 0);
        let empty = self
            .fb
            .ins()
            .iconst(I64, i64::from(layout::data_layout(len, 0)));
        self.fb.ins().store(self.trusted, empty, object, 8);
        if len > layout::INLINE_FIELDS
            && fields.iter().any(|(_, h)| matches!(h, Heapness::Array(_)))
        {
            let masks = self
                .fb
                .ins()
                .iadd_imm_s(object, as_i64(HEADER as usize + 8 * len)?);
            self.zero_words(masks, len.div_ceil(64))?;
        }
        self.fill_data(object, fields)?;
        Ok(object)
    }

    /// Stores the fields of a data object of these fields, each after the last, and the bits of
    /// its heap words: its layout word (`stilt_runtime::layout::data_layout`), or for a large
    /// object, its masks after its fields. The layout word or the masks of an object that holds
    /// an array in memory have none of its bits already, and get those of its heap words, the
    /// arrays' in a loop.
    fn fill_data(&mut self, object: Value, fields: &[(Operand, Heapness)]) -> Result<(), String> {
        let (at, len) = offsets(fields.iter().map(|(_, h)| match h {
            Heapness::Array(e) => Repr::Array(*e),
            _ => Repr::Scalar,
        }));
        let arrays = fields.iter().any(|(_, h)| matches!(h, Heapness::Array(_)));
        let mut masks: Vec<(u64, Vec<(Value, u32)>)> = vec![(0, Vec::new()); len.div_ceil(64)];
        let large = len > layout::INLINE_FIELDS;
        let mask_at = if large {
            HEADER as usize + 8 * len
        } else {
            layout::LAYOUT as usize
        };
        for ((field, heap), &i) in fields.iter().zip(&at) {
            let offset = i32::try_from(HEADER as usize + 8 * i).map_err(|e| e.to_string())?;
            let bit = u32::try_from(i % 64).expect("under 64");
            match heap {
                Heapness::Array(e) => {
                    self.fill_array(object, (offset, i), field, *e, mask_at)?;
                    continue;
                }
                Heapness::Static(true) => masks[i / 64].0 |= 1 << bit,
                Heapness::Static(false) => {}
                Heapness::Witness(w) => {
                    let witness = self.use_local(*w);
                    let heap = self.fb.ins().band_imm_u(witness, 1);
                    masks[i / 64].1.push((heap, bit));
                }
            }
            let v = self.held(field)?;
            self.fb.ins().store(self.trusted, v, object, offset);
        }
        for (j, (bits, dynamic)) in masks.into_iter().enumerate() {
            if large && arrays && bits == 0 && dynamic.is_empty() {
                continue;
            }
            let offset = i32::try_from(mask_at + 8 * j).map_err(|e| e.to_string())?;
            let bits = if large {
                bits
            } else {
                u64::from(layout::data_layout(len, bits))
            };
            let mut mask = self.fb.ins().iconst(I64, bits.cast_signed());
            if arrays {
                let set = self.fb.ins().load(I64, self.trusted, object, offset);
                mask = self.fb.ins().bor(mask, set);
            }
            for (witness, bit) in dynamic {
                let shifted = self.fb.ins().ishl_imm_u(witness, i64::from(bit));
                mask = self.fb.ins().bor(mask, shifted);
            }
            self.fb.ins().store(self.trusted, mask, object, offset);
        }
        Ok(())
    }

    /// Copies an array field's words to byte `offset` of a data object, word `i` of it, and sets
    /// the bits of its heap words in the word or the masks at byte `mask_at` of the object.
    fn fill_array(
        &mut self,
        object: Value,
        (offset, i): (i32, usize),
        field: &Operand,
        e: stilt_mir::mir::Elements<Repr>,
        mask_at: usize,
    ) -> Result<(), String> {
        let to = self.fb.ins().iadd_imm_s(object, i64::from(offset));
        match field {
            Operand::Local(_) => {
                let from = self.operand(field)?;
                self.copy_words(to, from, e.words())?;
            }
            Operand::Const(_) => self.zero_words(to, e.words())?,
        }
        let base = self.fb.ins().iadd_imm_s(object, as_i64(mask_at)?);
        self.mask_array(base, i, e)
    }

    /// A variant's index: an immediate's own, or the tag in its object's header.
    fn tag(&mut self, v: Value) -> Value {
        let (immediate, object, join) = (
            self.fb.create_block(),
            self.fb.create_block(),
            self.fb.create_block(),
        );
        self.fb.append_block_param(join, I64);
        let low = self.fb.ins().band_imm_u(v, 1);
        self.fb.ins().brif(low, immediate, &[], object, &[]);
        self.fb.switch_to_block(immediate);
        let index = self.fb.ins().ushr_imm_u(v, 1);
        self.fb.ins().jump(join, &[index.into()]);
        self.fb.switch_to_block(object);
        let tag = self.fb.ins().load(I16, self.trusted, v, 6);
        let tag = self.fb.ins().uextend(I64, tag);
        self.fb.ins().jump(join, &[tag.into()]);
        self.fb.switch_to_block(join);
        self.fb.block_params(join)[0]
    }

    /// Word `k` of a constant's value, of the words `words`, as a value of type `ty`, computed by
    /// its code where it is first used (declarations.constant-evaluation), which writes the words
    /// to the constant's cell, after the word that tells whether it is computed, through memory
    /// when they don't fit in registers.
    fn constant(
        &mut self,
        f: &FnRef,
        loc: &Operand,
        (k, words): (u32, &[Repr]),
        ty: Type,
    ) -> Result<Value, String> {
        let at = self.constant_value(f, loc, (k, words))?;
        Ok(self.fb.ins().load(ty, self.trusted, at, 0))
    }

    /// The address of value `k` of a constant's value, of the words `words`, computed by its code
    /// where it is first used (declarations.constant-evaluation), which writes the words to the
    /// constant's cell, after the word that tells whether it is computed, through memory when they
    /// don't fit in registers.
    pub(crate) fn constant_value(
        &mut self,
        f: &FnRef,
        loc: &Operand,
        (k, words): (u32, &[Repr]),
    ) -> Result<Value, String> {
        let id = self.reg.constant(self.module, f, words)?;
        let gv = self.module.declare_data_in_func(id, self.fb.func);
        let addr = self.fb.ins().symbol_value(I64, gv);
        // The load acquires the words that the thread which computed them released, and the
        // state is 1 once it is computed and 2 while a thread claims it, so a test of its low
        // bit, one instruction that branches, tells whether the words can be read.
        let state = self.fb.ins().atomic_load(I64, self.trusted, addr);
        let done = self.fb.ins().band_imm_u(state, 1);
        let not_done = self.fb.ins().icmp_imm_s(IntCC::Equal, done, 0);
        let loc = self.operand(loc)?;
        self.when(not_done, |t| {
            let mine = t
                .runtime("stilt_rt_constant_claim", &[addr], true)?
                .ok_or("a claim's result")?;
            t.when(mine, |t| t.compute_constant(f, loc, addr, words))
        })?;
        let (at, _) = offsets(words.iter().copied());
        let at = 8 + 8 * at.get(k as usize).copied().unwrap_or(0);
        Ok(self.fb.ins().iadd_imm_s(addr, crate::arrays::as_i64(at)?))
    }

    /// Computes a constant that the current thread claimed into its cell at `addr`, marks what
    /// its value reaches shared, since every thread may read it, and says it is computed
    /// (`stilt_runtime`'s `constants`). A constant's type names no type parameter
    /// (declarations.constant-declarations), so each word's representation is known.
    fn compute_constant(
        &mut self,
        f: &FnRef,
        loc: Value,
        addr: Value,
        words: &[Repr],
    ) -> Result<(), String> {
        let code = self.slot_code(f, &[])?;
        let n = offsets(words.iter().copied()).1;
        let sig = self.fb.import_signature(signature(self.module, 1, n));
        let value_at = self.fb.ins().iadd_imm_s(addr, 8);
        if in_memory(self.module, n) {
            self.fb.ins().call_indirect(sig, code, &[loc, value_at]);
        } else {
            let call = self.fb.ins().call_indirect(sig, code, &[loc]);
            let results = self.fb.inst_results(call)[..n].to_vec();
            for (i, value) in results.into_iter().enumerate() {
                let at = i32::try_from(8 + 8 * i).expect("a constant under 2 GB");
                self.fb.ins().store(self.trusted, value, addr, at);
            }
        }
        let (at, _) = offsets(words.iter().copied());
        for (repr, i) in words.iter().zip(at) {
            let at = i32::try_from(8 + 8 * i).expect("a constant under 2 GB");
            match *repr {
                Repr::Heap => {
                    let word = self.fb.ins().load(I64, self.trusted, addr, at);
                    self.runtime("stilt_rt_constant_share", &[word], false)?;
                }
                Repr::Array(e) => {
                    let base = self.fb.ins().iadd_imm_s(addr, i64::from(at));
                    self.each_counted(base, e, &mut |t, a, _, _| {
                        let word = t.fb.ins().load(I64, t.trusted, a, 0);
                        t.runtime("stilt_rt_constant_share", &[word], false)?;
                        Ok(())
                    })?;
                }
                Repr::Scalar | Repr::Generic(_) => {}
            }
        }
        self.runtime("stilt_rt_constant_done", &[addr], false)?;
        Ok(())
    }
}
