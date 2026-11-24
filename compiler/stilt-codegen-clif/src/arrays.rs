//! Arrays held in memory (generics.large-arrays; `stilt_mir::mir::Repr::Array`): a local of such a
//! representation lives in a slot of the frame, and the value of an operand that names it is
//! the address of its words. Assigning one copies the words it is given, from another local, a
//! pointer, an object's field, a constant's cell or a list's element, by one call of the
//! runtime; and copying, releasing, sharing and marking its counted words are loops over its
//! elements, with code for each counted word of an element only, so that the code is the same
//! whatever the array's size.

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::types::I64;
use cranelift_codegen::ir::{InstBuilder, Value};
use stilt_mir::mir::{Elements, Local, Operand, Repr, Runtime, Rvalue, offsets};

use crate::lists::constant;
use crate::translate::Translator;

/// What code does with each counted word of an array: given its address, its index among the
/// array's words, and its representation, a heap word or a word of a type parameter.
pub(crate) type EachWord<'f, 'a, 'b> =
    dyn FnMut(&mut Translator<'a, 'b>, Value, Value, Repr) -> Result<(), String> + 'f;

impl<'a, 'b> Translator<'a, 'b> {
    /// The layout of the array that a local holds in memory, if it holds one.
    pub(crate) fn array_of(&self, l: Local) -> Option<Elements<Repr>> {
        match self.repr(l) {
            Repr::Array(e) => Some(e),
            _ => None,
        }
    }

    /// The array that an operand names, if it names a local that holds one in memory.
    pub(crate) fn array_operand(&self, o: &Operand) -> Option<Elements<Repr>> {
        o.local().and_then(|l| self.array_of(l))
    }

    /// The number of words of memory that a value of these locals takes.
    pub(crate) fn words_of_locals(&self, locals: &[Local]) -> usize {
        offsets(locals.iter().map(|&l| self.repr(l))).1
    }

    /// The word offset of each operand in memory, one after the other, and the words they take:
    /// an array its words, and any other one.
    pub(crate) fn operand_offsets(&self, os: &[Operand]) -> (Vec<usize>, usize) {
        offsets(os.iter().map(|o| match self.array_operand(o) {
            Some(e) => Repr::Array(e),
            None => Repr::Scalar,
        }))
    }

    /// Copies `words` words from `from` to `to`, which don't overlap.
    pub(crate) fn copy_words(
        &mut self,
        to: Value,
        from: Value,
        words: usize,
    ) -> Result<(), String> {
        let n = i64::try_from(words).map_err(|e| e.to_string())?;
        let n = self.fb.ins().iconst(I64, n);
        self.runtime("stilt_rt_copy_words", &[to, from, n], false)?;
        Ok(())
    }

    /// Sets `words` words at `to` to 0.
    pub(crate) fn zero_words(&mut self, to: Value, words: usize) -> Result<(), String> {
        let n = i64::try_from(words).map_err(|e| e.to_string())?;
        let n = self.fb.ins().iconst(I64, n);
        self.runtime("stilt_rt_zero_words", &[to, n], false)?;
        Ok(())
    }

    /// Gives the array local `array` of the layout `e` the words of the rvalue `r`, which a
    /// statement assigns it: those it copies, or none for a constant, which clears it.
    pub(crate) fn assign_array(
        &mut self,
        array: Local,
        e: Elements<Repr>,
        r: &Rvalue,
    ) -> Result<(), String> {
        let to = self.slot_addr(array);
        let from = match r {
            Rvalue::Use(Operand::Const(_)) => return self.zero_words(to, e.words()),
            Rvalue::Use(o) | Rvalue::Load(o) => self.operand(o)?,
            Rvalue::Field { base, index, .. } => {
                let b = self.operand(base)?;
                self.field_addr(b, *index)
            }
            Rvalue::Constant(f, loc, k, words, _) => self.constant_value(f, loc, (*k, words))?,
            Rvalue::Runtime(f, args) => self.array_in_runtime(*f, args)?,
            _ => return Err(format!("an array in memory from {r:?}")),
        };
        self.copy_words(to, from, e.words())
    }

    /// The address of the words of an array that a runtime function reads in place: an
    /// element of a list, or of a key or a value of a map.
    fn array_in_runtime(&mut self, f: Runtime, args: &[Operand]) -> Result<Value, String> {
        let word = |o: &Operand| constant(o).ok_or_else(|| format!("a constant, not {o:?}"));
        match (f, args) {
            (Runtime::ListAt, [list, i, elem, at]) => {
                let (list, i) = (self.operand(list)?, self.operand(i)?);
                Ok(self.element_addr(list, i, word(elem)?, word(at)?))
            }
            (Runtime::ListIndex, [loc, list, i, elem, at]) => {
                let (list, i) = (self.operand(list)?, self.operand(i)?);
                self.checked_element(loc, (list, i), word(elem)?, word(at)?)
            }
            (Runtime::MapWord, [_, pointer, at]) => {
                let p = self.operand(pointer)?;
                let bytes = i64::try_from(8 * word(at)?).map_err(|e| e.to_string())?;
                Ok(self.fb.ins().iadd_imm_s(p, bytes))
            }
            _ => Err(format!("an array in memory from {f:?}")),
        }
    }

    /// Runs `f` on each word of an array of the layout `e` at `base` that may need its
    /// references counted, in a loop over its elements: with its address, its index among the
    /// array's words, and its representation.
    pub(crate) fn each_counted(
        &mut self,
        base: Value,
        e: Elements<Repr>,
        f: &mut EachWord<'_, 'a, 'b>,
    ) -> Result<(), String> {
        if !e.counted() {
            return Ok(());
        }
        let width = e.element_words();
        let (at, _) = offsets(e.each().iter().copied());
        let i = self.fb.declare_var(I64);
        let zero = self.fb.ins().iconst(I64, 0);
        self.fb.def_var(i, zero);
        let (head, body, exit) = (
            self.fb.create_block(),
            self.fb.create_block(),
            self.fb.create_block(),
        );
        self.fb.ins().jump(head, &[]);
        self.fb.switch_to_block(head);
        let index = self.fb.use_var(i);
        let more = self
            .fb
            .ins()
            .icmp_imm_u(IntCC::UnsignedLessThan, index, i64::from(e.len()));
        self.fb.ins().brif(more, body, &[], exit, &[]);
        self.fb.switch_to_block(body);
        let index = self.fb.use_var(i);
        let first = self.fb.ins().imul_imm_s(index, as_i64(width)?);
        let bytes = self.fb.ins().ishl_imm_u(first, 3);
        let element = self.fb.ins().iadd(base, bytes);
        for (&r, &k) in e.each().iter().zip(&at) {
            let addr = self.fb.ins().iadd_imm_s(element, 8 * as_i64(k)?);
            let word = self.fb.ins().iadd_imm_s(first, as_i64(k)?);
            match r {
                Repr::Scalar => {}
                Repr::Heap | Repr::Generic(_) => f(self, addr, word, r)?,
                Repr::Array(inner) => {
                    let mut nested = |t: &mut Self, a: Value, w: Value, r: Repr| {
                        let w = t.fb.ins().iadd(word, w);
                        f(t, a, w, r)
                    };
                    self.each_counted(addr, inner, &mut nested)?;
                }
            }
        }
        let index = self.fb.use_var(i);
        let next = self.fb.ins().iadd_imm_s(index, 1);
        self.fb.def_var(i, next);
        self.fb.ins().jump(head, &[]);
        self.fb.switch_to_block(exit);
        Ok(())
    }

    /// Counts a reference, or releases one, of each counted word of an array of the layout
    /// `e` at `base`.
    pub(crate) fn count_array(
        &mut self,
        base: Value,
        e: Elements<Repr>,
        dup: bool,
    ) -> Result<(), String> {
        self.each_counted(base, e, &mut |t, addr, _, r| {
            let word = t.fb.ins().load(I64, t.trusted, addr, 0);
            t.count(word, r, dup)
        })
    }

    /// Sets, in the masks at `masks`, the bit of each heap word of an array of the layout `e`
    /// whose first word is word `start` of the data object.
    pub(crate) fn mask_array(
        &mut self,
        masks: Value,
        start: usize,
        e: Elements<Repr>,
    ) -> Result<(), String> {
        self.each_counted(masks, e, &mut |t, _, word, r| {
            let heap = match r {
                Repr::Generic(w) => {
                    let witness = t.use_local(w);
                    t.fb.ins().band_imm_u(witness, 1)
                }
                _ => t.fb.ins().iconst(I64, 1),
            };
            let word = t.fb.ins().iadd_imm_s(word, as_i64(start)?);
            let which = t.fb.ins().ushr_imm_u(word, 6);
            let at = t.fb.ins().ishl_imm_u(which, 3);
            let at = t.fb.ins().iadd(masks, at);
            let bit = t.fb.ins().band_imm_u(word, 63);
            let shifted = t.fb.ins().ishl(heap, bit);
            let mask = t.fb.ins().load(I64, t.trusted, at, 0);
            let mask = t.fb.ins().bor(mask, shifted);
            t.fb.ins().store(t.trusted, mask, at, 0);
            Ok(())
        })
    }
}

impl Translator<'_, '_> {
    /// The shape of a value made of parts, each a number of values of a shape, which `parts`
    /// gives in pairs, as the runtime makes it.
    pub(crate) fn shape_parts(&mut self, parts: &[Operand]) -> Result<Value, String> {
        let slot = self.words_slot(parts.len());
        for (k, p) in parts.iter().enumerate() {
            let v = self.operand(p)?;
            let offset = i32::try_from(8 * k).map_err(|e| e.to_string())?;
            self.fb.ins().stack_store(I64, v, slot, offset);
        }
        let memory = self.fb.ins().stack_addr(I64, slot, 0);
        let n = self.fb.ins().iconst(I64, as_i64(parts.len() / 2)?);
        self.runtime("stilt_rt_shape_parts", &[memory, n], true)?
            .ok_or_else(|| "a shape".to_owned())
    }
}

/// A size or an offset as an immediate.
pub(crate) fn as_i64(n: usize) -> Result<i64, String> {
    i64::try_from(n).map_err(|e| e.to_string())
}
