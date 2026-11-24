//! The runtime's fast paths, compiled inline: counting a reference and releasing one, and
//! making the object of a slot unique before a write, each calling the runtime only on its slow
//! path, which is laid out cold (goal debug-speed: cheap debug optimizations); those of lists
//! are in [`crate::lists`]. An object that threads share takes the slow path, where the runtime
//! counts it by atomic instructions and copies it before a write, so the fast path adds one test of
//! a bit of the word it loads the count from (goal atomic-counts-where-shared). They read objects
//! by the layout `stilt_runtime::layout` gives, and change nothing a user function's code depends
//! on, so each function can still be patched alone.

#[cfg(test)]
mod tests;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::types::{I32, I64};
use cranelift_codegen::ir::{InstBuilder, Value};
use stilt_runtime::layout;

use crate::translate::Translator;

impl Translator<'_, '_> {
    /// Whether a heap word is a pointer to an object, rather than an immediate.
    fn is_pointer(&mut self, word: Value) -> Value {
        let low = self
            .fb
            .ins()
            .band_imm_u(word, i64::from(layout::ALIGN_BITS));
        let aligned = self.fb.ins().icmp_imm_s(IntCC::Equal, low, 0);
        let nonzero = self.fb.ins().icmp_imm_s(IntCC::NotEqual, word, 0);
        self.fb.ins().band(aligned, nonzero)
    }

    /// The word of an object's header that holds its count, in its low 32 bits, and its flags,
    /// and whether threads share the object, whose count only the runtime then changes, by
    /// atomic instructions: one load, and a test of one bit that branches.
    pub(crate) fn count_word(&mut self, object: Value) -> (Value, Value) {
        let word = self.fb.ins().load(I64, self.trusted, object, layout::RC);
        let shared = self
            .fb
            .ins()
            .band_imm_u(word, layout::SHARED_BIT.cast_signed());
        (word, shared)
    }

    /// Runs `plain` on the count of an object that threads don't share, and otherwise calls the
    /// runtime function `shared`, laid out cold, on the object.
    fn counted(
        &mut self,
        object: Value,
        shared: &str,
        plain: impl FnOnce(&mut Self, Value) -> Result<(), String>,
    ) -> Result<(), String> {
        let (word, is_shared) = self.count_word(object);
        let (here, cold, join) = (
            self.fb.create_block(),
            self.fb.create_block(),
            self.fb.create_block(),
        );
        self.fb.set_cold_block(cold);
        self.fb.ins().brif(is_shared, cold, &[], here, &[]);
        self.fb.switch_to_block(cold);
        self.runtime(shared, &[object], false)?;
        self.fb.ins().jump(join, &[]);
        self.fb.switch_to_block(here);
        let rc = self.fb.ins().ireduce(I32, word);
        plain(self, rc)?;
        self.fb.ins().jump(join, &[]);
        self.fb.switch_to_block(join);
        Ok(())
    }

    /// Counts one more reference to a heap word: its object's count goes up, unless the word
    /// is an immediate or its object is immortal.
    pub(crate) fn retain(&mut self, word: Value) -> Result<(), String> {
        let pointer = self.is_pointer(word);
        self.when(pointer, |t| {
            t.counted(word, "stilt_rt_dup", |t, rc| {
                t.when(rc, |t| {
                    let more = t.fb.ins().iadd_imm_s(rc, 1);
                    t.fb.ins().store(t.trusted, more, word, layout::RC);
                    Ok(())
                })
            })
        })
    }

    /// Releases a reference to a heap word: its object's count goes down, and the runtime
    /// frees the object when that was its last reference. A block that raises, which a
    /// function takes only on its failure, calls the runtime for each release instead: the
    /// blocks of each fast path, which it would multiply, are most of what the register
    /// allocator has to cover in a function that releases many words on its way out, such as an
    /// instance of `json.read` for a record of many words.
    pub(crate) fn release(&mut self, word: Value) -> Result<(), String> {
        if self.raising && std::env::var_os("STILT_OLD_RELEASE").is_none() {
            return self.runtime("stilt_rt_drop", &[word], false).map(|_| ());
        }
        let pointer = self.is_pointer(word);
        self.when(pointer, |t| {
            t.counted(word, "stilt_rt_drop", |t, rc| {
                let (many, last, join) = (
                    t.fb.create_block(),
                    t.fb.create_block(),
                    t.fb.create_block(),
                );
                let more_than_one = t.fb.ins().icmp_imm_u(IntCC::UnsignedGreaterThan, rc, 1);
                t.fb.ins().brif(more_than_one, many, &[], last, &[]);
                t.fb.switch_to_block(many);
                let less = t.fb.ins().iadd_imm_s(rc, -1);
                t.fb.ins().store(t.trusted, less, word, layout::RC);
                t.fb.ins().jump(join, &[]);
                t.fb.switch_to_block(last);
                let one = t.fb.ins().icmp_imm_s(IntCC::Equal, rc, 1);
                t.when(one, |t| {
                    t.runtime("stilt_rt_drop", &[word], false).map(|_| ())
                })?;
                t.fb.ins().jump(join, &[]);
                t.fb.switch_to_block(join);
                Ok(())
            })
        })
    }

    /// `fast` if `object` is unique, nothing else referencing it and threads not sharing it, and
    /// otherwise the result of `slow`, which calls the runtime and is laid out cold: a write
    /// changes an object in place only then.
    pub(crate) fn if_unique(
        &mut self,
        object: Value,
        fast: impl FnOnce(&mut Self) -> Value,
        slow: impl FnOnce(&mut Self) -> Result<Value, String>,
    ) -> Result<Value, String> {
        let (word, shared) = self.count_word(object);
        let (count, yes, no, join) = (
            self.fb.create_block(),
            self.fb.create_block(),
            self.fb.create_block(),
            self.fb.create_block(),
        );
        let result = self.fb.append_block_param(join, I64);
        self.fb.set_cold_block(no);
        self.fb.ins().brif(shared, no, &[], count, &[]);
        self.fb.switch_to_block(count);
        let rc = self.fb.ins().ireduce(I32, word);
        let unique = self.fb.ins().icmp_imm_s(IntCC::Equal, rc, 1);
        self.fb.ins().brif(unique, yes, &[], no, &[]);
        self.fb.switch_to_block(yes);
        let v = fast(self);
        self.fb.ins().jump(join, &[v.into()]);
        self.fb.switch_to_block(no);
        let v = slow(self)?;
        self.fb.ins().jump(join, &[v.into()]);
        self.fb.switch_to_block(join);
        Ok(result)
    }

    /// The object a slot holds, made unique: itself if nothing else references it, and
    /// otherwise the runtime's copy.
    pub(crate) fn unique(&mut self, slot: Value) -> Result<Value, String> {
        let object = self.fb.ins().load(I64, self.trusted, slot, 0);
        self.if_unique(
            object,
            |_| object,
            |t| result(t.runtime("stilt_rt_unique", &[slot], true)),
        )
    }
}

fn result(value: Result<Option<Value>, String>) -> Result<Value, String> {
    value?.ok_or_else(|| "a runtime function without a result".to_owned())
}
