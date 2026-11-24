//! The fast paths of lists, compiled inline (goals debug-speed and inline-values): reading a word
//! of an element, a pointer to an element of a unique list, storing a narrow scalar, appending an
//! element and popping one, and reading an element of a type parameter's in its one word. Each
//! calls the runtime only on its slow path, laid out cold, or on its failure path
//! ([`crate::cold`]); an element read or written at an index that `stilt_mir`'s optimizer proved
//! in bounds has no failure path.
//!
//! A list holds each element in the size its shape gives (`stilt_mir::shape`): code that names
//! the element type passes the shape as a constant, so an element's words are at fixed offsets
//! and a narrow scalar is loaded and stored in its width; generic code passes the witness of the
//! type parameter, and reads an element of one word inline and any other through the runtime.

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::types::{I8, I16, I32, I64};
use cranelift_codegen::ir::{InstBuilder, Type, Value};
use stilt_mir::FnRef;
use stilt_mir::mir::{Arg, Const, Operand};
use stilt_mir::shape;
use stilt_runtime::layout;

use crate::arrays::as_i64;
use crate::module::native_symbol;
use crate::translate::Translator;

#[cfg(test)]
mod tests;
mod writes;

/// The words of an element that code appends to a list: each in a value, or `n` of them in
/// memory, where this address points.
enum Element {
    Words(Vec<Value>),
    Memory(Value, usize),
}

/// The value of a constant word.
pub(crate) fn constant(o: &Operand) -> Option<u64> {
    match o {
        Operand::Const(Const::Word(w)) => Some(*w),
        _ => None,
    }
}

/// The type a narrow scalar of this shape is loaded and stored as, if it is one, and whether
/// its loads extend its sign.
fn narrow(shape: u64) -> Option<(Type, bool)> {
    let ty = match shape::size(shape) {
        1 => I8,
        2 => I16,
        4 => I32,
        _ => return None,
    };
    Some((ty, shape::signed(shape)))
}

/// The immediate of `Option`'s variant of this index: `None`, then `Some` (std.bytes-and-scalars).
fn option_tag(index: i64) -> i64 {
    index << 1 | 1
}

impl Translator<'_, '_> {
    /// The number of elements of a list.
    pub(crate) fn list_len(&mut self, list: Value) -> Value {
        self.fb
            .ins()
            .load(I64, self.trusted, list, layout::LIST_LEN)
    }

    /// The address of word `word` of element `i` of a list of elements of the shape `shape`.
    fn element(&mut self, list: Value, i: Value, shape: u64, word: u64) -> Value {
        let data = self
            .fb
            .ins()
            .load(I64, self.trusted, list, layout::LIST_DATA);
        let size = shape::size(shape);
        let offset = if size.is_power_of_two() {
            self.fb
                .ins()
                .ishl_imm_u(i, i64::from(size.trailing_zeros()))
        } else {
            self.fb.ins().imul_imm_s(i, size.cast_signed())
        };
        let at = self.fb.ins().iadd(data, offset);
        if word == 0 {
            return at;
        }
        self.fb.ins().iadd_imm_s(at, (8 * word).cast_signed())
    }

    /// The word at `addr` of an element of the shape `shape`, as a value of type `ty`: a narrow
    /// scalar widened as its kind is.
    fn load_element(&mut self, addr: Value, shape: u64, ty: Type) -> Value {
        match narrow(shape) {
            Some((I8, false)) => self.fb.ins().uload8(I64, self.trusted, addr, 0),
            Some((I8, true)) => self.fb.ins().sload8(I64, self.trusted, addr, 0),
            Some((I16, false)) => self.fb.ins().uload16(I64, self.trusted, addr, 0),
            Some((I16, true)) => self.fb.ins().sload16(I64, self.trusted, addr, 0),
            Some((_, false)) => self.fb.ins().uload32(self.trusted, addr, 0),
            Some((_, true)) => self.fb.ins().sload32(self.trusted, addr, 0),
            None => self.fb.ins().load(ty, self.trusted, addr, 0),
        }
    }

    /// Word `word` of element `i`, in bounds, of a list of elements of the shape `shape`,
    /// borrowed, as a value of type `ty`.
    pub(crate) fn list_at(
        &mut self,
        list: Value,
        i: Value,
        shape: u64,
        word: u64,
        ty: Type,
    ) -> Value {
        let addr = self.element(list, i, shape, word);
        self.load_element(addr, shape, ty)
    }

    /// Ends the program with the runtime's panic at `loc` when `i` is out of bounds of a list
    /// of `len` elements: `fail` calls the runtime with the location, which reports it.
    fn bounds(
        &mut self,
        loc: &Operand,
        i: Value,
        len: Value,
        fail: impl FnOnce(&mut Self, Value) -> Result<(), String>,
    ) -> Result<(), String> {
        let outside = self
            .fb
            .ins()
            .icmp(IntCC::UnsignedGreaterThanOrEqual, i, len);
        self.fail_if(outside, |t| {
            let loc = t.operand(loc)?;
            fail(t, loc)
        })
    }

    /// Word `word` of `xs[i]`, borrowed, as a value of type `ty`, if `i` is in bounds, and
    /// otherwise the runtime's panic.
    pub(crate) fn list_index(
        &mut self,
        loc: &Operand,
        list: Value,
        i: Value,
        (shape, word): (u64, u64),
        ty: Type,
    ) -> Result<Value, String> {
        let len = self.list_len(list);
        self.bounds(loc, i, len, |t, loc| {
            t.runtime("stilt_rt_list_index", &[loc, list, i], true)
                .map(|_| ())
        })?;
        Ok(self.list_at(list, i, shape, word, ty))
    }

    /// The address of word `word` of element `i`, in bounds, of a list of elements of the
    /// shape `shape`: where an array held in memory in the element starts.
    pub(crate) fn element_addr(&mut self, list: Value, i: Value, shape: u64, word: u64) -> Value {
        self.element(list, i, shape, word)
    }

    /// The address of word `word` of `xs[i]`, if `i` is in bounds, and otherwise the runtime's
    /// panic.
    pub(crate) fn checked_element(
        &mut self,
        loc: &Operand,
        (list, i): (Value, Value),
        shape: u64,
        word: u64,
    ) -> Result<Value, String> {
        let len = self.list_len(list);
        self.bounds(loc, i, len, |t, loc| {
            t.runtime("stilt_rt_list_index", &[loc, list, i], true)
                .map(|_| ())
        })?;
        Ok(self.element(list, i, shape, word))
    }

    /// `ListPush (list, elem, words..)`: appends an element to a list that nothing else
    /// references, inline when the list has room, and otherwise through the runtime.
    pub(crate) fn list_push(&mut self, args: &[Operand]) -> Result<(), String> {
        let [list, elem, words @ ..] = args else {
            return Err("a push of a list and a shape".to_owned());
        };
        let list = self.operand(list)?;
        let words = self.element_words(words)?;
        let room = self.has_room(list);
        let runtime = ("stilt_rt_list_push_words", "stilt_rt_list_push");
        self.append((room, None), (list, list), elem, &words, runtime)
    }

    /// `ListAppend (slot, elem, words..)`: appends an element to the list a slot holds, in place
    /// when the list is unique and has room, and otherwise once the runtime has made it so.
    pub(crate) fn list_append(&mut self, args: &[Operand]) -> Result<(), String> {
        let [slot, elem, words @ ..] = args else {
            return Err("an append to a slot and a shape".to_owned());
        };
        let slot = self.operand(slot)?;
        let words = self.element_words(words)?;
        let list = self.fb.ins().load(I64, self.trusted, slot, 0);
        let room = self.has_room(list);
        let (word, shared) = self.count_word(list);
        let rc = self.fb.ins().ireduce(I32, word);
        let unique = self.fb.ins().icmp_imm_s(IntCC::Equal, rc, 1);
        let ready = self.fb.ins().band(room, unique);
        let runtime = ("stilt_rt_list_append_words", "stilt_rt_list_append_value");
        self.append((ready, Some(shared)), (list, slot), elem, &words, runtime)
    }

    /// Whether a list has room for one more element.
    fn has_room(&mut self, list: Value) -> Value {
        let len = self.list_len(list);
        let cap = self
            .fb
            .ins()
            .load(I64, self.trusted, list, layout::LIST_CAP);
        self.fb.ins().icmp(IntCC::UnsignedLessThan, len, cap)
    }

    /// The words of an element's operands, an `f64` moved to a word.
    fn words_of(&mut self, words: &[Operand]) -> Result<Vec<Value>, String> {
        words.iter().map(|w| self.operand(w)).collect()
    }

    /// The words of an element appended to a list, from its operands: their values, or for an
    /// element that holds an array in memory, all its words in memory of their own.
    fn element_words(&mut self, words: &[Operand]) -> Result<Element, String> {
        if !words.iter().any(|w| self.array_operand(w).is_some()) {
            return self.words_of(words).map(Element::Words);
        }
        let (at, n) = self.operand_offsets(words);
        let slot = self.words_slot(n);
        let memory = self.fb.ins().stack_addr(I64, slot, 0);
        for (w, i) in words.iter().zip(at) {
            let v = self.operand(w)?;
            if let Some(e) = self.array_operand(w) {
                let to = self.fb.ins().iadd_imm_s(memory, 8 * as_i64(i)?);
                self.copy_words(to, v, e.words())?;
            } else {
                let offset = i32::try_from(8 * i).map_err(|e| e.to_string())?;
                self.fb.ins().stack_store(I64, v, slot, offset);
            }
        }
        Ok(Element::Memory(memory, n))
    }

    /// Appends an element's words to `list` inline if `ready`, and threads don't share the list
    /// when `shared` tells whether they do, and otherwise, laid out cold,
    /// through the runtime, which takes `target`, the list or its slot: for an element of the
    /// constant shape `elem`, `by_words` takes a pointer to its words in memory, and for a value
    /// of a type parameter, whose witness `elem` is, `by_value` takes its one word, and only an
    /// element of one word is stored inline. No value has to survive the call, so the register
    /// allocator keeps the hot path's values in registers.
    fn append(
        &mut self,
        (ready, shared): (Value, Option<Value>),
        (list, target): (Value, Value),
        elem: &Operand,
        words: &Element,
        (by_words, by_value): (&str, &str),
    ) -> Result<(), String> {
        let (shape, ready) = if let Some(shape) = constant(elem) {
            (shape, ready)
        } else {
            let witness = self.operand(elem)?;
            let one_word = self.one_word(witness);
            (shape::word(false), self.fb.ins().band(ready, one_word))
        };
        let (fast, cold, join) = (
            self.fb.create_block(),
            self.fb.create_block(),
            self.fb.create_block(),
        );
        self.fb.set_cold_block(cold);
        if let Some(shared) = shared {
            let check = self.fb.create_block();
            self.fb.ins().brif(shared, cold, &[], check, &[]);
            self.fb.switch_to_block(check);
        }
        self.fb.ins().brif(ready, fast, &[], cold, &[]);
        self.fb.switch_to_block(fast);
        self.store_last(list, shape, words)?;
        self.fb.ins().jump(join, &[]);
        self.fb.switch_to_block(cold);
        match words {
            Element::Memory(memory, _) => {
                self.runtime(by_words, &[target, *memory], false)?;
            }
            Element::Words(words) if constant(elem).is_some() => {
                let memory = self.in_memory(words)?;
                self.runtime(by_words, &[target, memory], false)?;
            }
            Element::Words(words) => {
                let x = *words.first().ok_or("a push of a value")?;
                self.runtime(by_value, &[target, x], false)?;
            }
        }
        self.fb.ins().jump(join, &[]);
        self.fb.switch_to_block(join);
        Ok(())
    }

    /// Whether a witness says its values take one word in a list.
    fn one_word(&mut self, witness: Value) -> Value {
        let size = self
            .fb
            .ins()
            .ushr_imm_u(witness, i64::from(shape::SIZE_SHIFT));
        let size = self
            .fb
            .ins()
            .band_imm_u(size, shape::SIZE_BITS.cast_signed());
        self.fb.ins().icmp_imm_s(IntCC::Equal, size, 8)
    }

    /// A pointer to the words in a stack slot of their own, which takes a multiple of 16
    /// bytes, as every slot does, so that the float spills after it stay aligned.
    fn in_memory(&mut self, words: &[Value]) -> Result<Value, String> {
        let slot = self.words_slot(words.len());
        for (k, &w) in words.iter().enumerate() {
            let offset = i32::try_from(8 * k).map_err(|e| e.to_string())?;
            self.fb.ins().stack_store(I64, w, slot, offset);
        }
        Ok(self.fb.ins().stack_addr(I64, slot, 0))
    }

    /// Stores an element's words after the last element of a list with room for it, which then
    /// holds it.
    fn store_last(&mut self, list: Value, shape: u64, words: &Element) -> Result<(), String> {
        let len = self.list_len(list);
        let addr = self.element(list, len, shape, 0);
        let words = match words {
            Element::Words(words) => words.as_slice(),
            Element::Memory(memory, n) => {
                self.copy_words(addr, *memory, *n)?;
                &[]
            }
        };
        for (k, &x) in words.iter().enumerate() {
            let offset = i32::try_from(8 * k).map_err(|e| e.to_string())?;
            if narrow(shape).is_some() {
                self.store_narrow(addr, x, shape);
            } else {
                self.fb.ins().store(self.trusted, x, addr, offset);
            }
        }
        let more = self.fb.ins().iadd_imm_s(len, 1);
        self.fb
            .ins()
            .store(self.trusted, more, list, layout::LIST_LEN);
        Ok(())
    }

    /// `xs[i]` of a list of values of a type parameter whose witness is `shape`, in the one
    /// word that holds it where a type parameter stands, with references of its own: an element
    /// of one word inline, counted if its witness says it is a heap word, and any other from
    /// the runtime, which widens a narrow scalar or boxes the words of a value held inline.
    pub(crate) fn list_get(
        &mut self,
        loc: &Operand,
        list: Value,
        i: Value,
        shape: Value,
    ) -> Result<Value, String> {
        let len = self.list_len(list);
        self.bounds(loc, i, len, |t, loc| {
            t.runtime("stilt_rt_list_get", &[loc, list, i], true)
                .map(|_| ())
        })?;
        let one_word = self.one_word(shape);
        let (fast, slow, join) = (
            self.fb.create_block(),
            self.fb.create_block(),
            self.fb.create_block(),
        );
        let x = self.fb.append_block_param(join, I64);
        self.fb.ins().brif(one_word, fast, &[], slow, &[]);
        self.fb.switch_to_block(fast);
        let word = self.list_at(list, i, shape::word(false), 0, I64);
        let heap = self.fb.ins().band_imm_u(shape, 1);
        self.when(heap, |t| t.retain(word))?;
        self.fb.ins().jump(join, &[word.into()]);
        self.fb.switch_to_block(slow);
        let loc = self.operand(loc)?;
        let boxed = result(self.runtime("stilt_rt_list_get", &[loc, list, i], true))?;
        self.fb.ins().jump(join, &[boxed.into()]);
        self.fb.switch_to_block(join);
        Ok(x)
    }

    /// The shape of a value of words of these operands, each 0 for a scalar, 1 for a heap word
    /// or the witness of a type parameter, whose lowest bit tells (`stilt_mir::shape`): the
    /// runtime makes that of a value of more than `shape::MASK_WORDS` words.
    pub(crate) fn shape_of(&mut self, words: &[Operand]) -> Result<Value, String> {
        let Some(fixed) = shape::of_words(&vec![false; words.len()]) else {
            let values = self.words_of(words)?;
            let memory = self.in_memory(&values)?;
            let n = i64::try_from(words.len()).map_err(|e| e.to_string())?;
            let n = self.fb.ins().iconst(I64, n);
            return result(self.runtime("stilt_rt_large_shape", &[memory, n], true));
        };
        let one = words.len() == 1;
        let mut shape = self.fb.ins().iconst(I64, fixed.cast_signed());
        for (k, w) in words.iter().enumerate() {
            let bit = i64::from(shape::MASK_SHIFT) + i64::try_from(k).map_err(|e| e.to_string())?;
            let heap = self.operand(w)?;
            let heap = self.fb.ins().band_imm_u(heap, 1);
            let at = self.fb.ins().ishl_imm_u(heap, bit);
            shape = self.fb.ins().bor(shape, at);
            if one {
                shape = self.fb.ins().bor(shape, heap);
            }
        }
        Ok(shape)
    }
}

impl Translator<'_, '_> {
    /// The results of a call of a native that the code computes inline, if it is one: a list's
    /// length, whether it is empty, and the pop of a list whose elements have a constant shape
    /// of at most a word.
    pub(crate) fn inline_native(
        &mut self,
        f: &FnRef,
        values: &[Value],
        args: &[Arg],
    ) -> Result<Option<Vec<Value>>, String> {
        // Each takes its location and its element type's witness, then the list, or the slot of
        // an `inout` one.
        let Some(&list) = values.get(2) else {
            return Ok(None);
        };
        Ok(match native_symbol(f).as_deref() {
            Some("stilt_std_prelude_List_len") => Some(vec![self.list_len(list)]),
            Some("stilt_std_prelude_List_is_empty") => {
                let len = self.list_len(list);
                let empty = self.fb.ins().icmp_imm_s(IntCC::Equal, len, 0);
                Some(vec![self.fb.ins().uextend(I64, empty)])
            }
            Some("stilt_std_prelude_List_pop") => match args.get(1) {
                Some(Arg::Borrow(o)) => match constant(o) {
                    Some(shape) if shape::size(shape) <= 8 => Some(self.pop(list, shape)?),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        })
    }

    /// `xs.pop()` on the list the slot `slot` holds, of elements of one word or narrower:
    /// `None` for an empty list, and otherwise `Some` of its last element, which moves out of the
    /// list once it is unique, as the runtime makes it if it is shared.
    fn pop(&mut self, slot: Value, shape: u64) -> Result<Vec<Value>, String> {
        let list = self.fb.ins().load(I64, self.trusted, slot, 0);
        let len = self.list_len(list);
        let (some, join) = (self.fb.create_block(), self.fb.create_block());
        let tag = self.fb.append_block_param(join, I64);
        let payload = self.fb.append_block_param(join, I64);
        let none = self.fb.ins().iconst(I64, option_tag(0));
        let zero = self.fb.ins().iconst(I64, 0);
        self.fb
            .ins()
            .brif(len, some, &[], join, &[none.into(), zero.into()]);
        self.fb.switch_to_block(some);
        let list = self.if_unique(
            list,
            |_| list,
            |t| result(t.runtime("stilt_rt_unique", &[slot], true)),
        )?;
        let shorter = self.fb.ins().iadd_imm_s(len, -1);
        self.fb
            .ins()
            .store(self.trusted, shorter, list, layout::LIST_LEN);
        let value = self.list_at(list, shorter, shape, 0, I64);
        let some_tag = self.fb.ins().iconst(I64, option_tag(1));
        self.fb.ins().jump(join, &[some_tag.into(), value.into()]);
        self.fb.switch_to_block(join);
        Ok(vec![tag, payload])
    }
}

fn result(value: Result<Option<Value>, String>) -> Result<Value, String> {
    value?.ok_or_else(|| "a runtime function without a result".to_owned())
}
