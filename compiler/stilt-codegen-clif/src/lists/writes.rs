//! The slots of elements written in place: a pointer to an element, its index checked or
//! proved in bounds, in a list made unique first unless `stilt_mir`'s optimizer proved it
//! unique already, and a narrow scalar stored through it.

use cranelift_codegen::ir::types::{I8, I16, I64};
use cranelift_codegen::ir::{InstBuilder, Value};
use stilt_mir::mir::Operand;

use super::{constant, narrow, result};
use crate::translate::Translator;

impl Translator<'_, '_> {
    /// A pointer to element `i` of the list a slot holds, of elements of the shape `shape`:
    /// the runtime's panic if `i` is out of bounds, and otherwise in place if the list is
    /// unique, or from the runtime, which copies the list.
    pub(crate) fn list_slot(
        &mut self,
        loc: &Operand,
        slot: Value,
        i: Value,
        shape: u64,
    ) -> Result<Value, String> {
        let list = self.fb.ins().load(I64, self.trusted, slot, 0);
        let len = self.list_len(list);
        self.bounds(loc, i, len, |t, loc| {
            t.runtime("stilt_rt_list_slot", &[loc, slot, i], true)
                .map(|_| ())
        })?;
        self.unique_element(list, i, shape, |t| {
            let loc = t.operand(loc)?;
            result(t.runtime("stilt_rt_list_slot", &[loc, slot, i], true))
        })
    }

    /// A pointer to element `i`, in bounds, of the list a slot holds, of elements of the shape
    /// `shape`: in place if the list is unique, and otherwise in the copy the runtime makes
    ///. Nothing is checked but the list's count.
    pub(crate) fn list_slot_at(
        &mut self,
        slot: Value,
        i: Value,
        shape: u64,
    ) -> Result<Value, String> {
        let list = self.fb.ins().load(I64, self.trusted, slot, 0);
        self.unique_element(list, i, shape, |t| {
            let copy = result(t.runtime("stilt_rt_unique", &[slot], true))?;
            Ok(t.element(copy, i, shape, 0))
        })
    }

    /// A pointer to element `i` of the list a slot holds, which nothing else references, of
    /// elements of the shape `shape`: the runtime's panic if `i` is out of bounds.
    pub(crate) fn list_element(
        &mut self,
        loc: &Operand,
        slot: Value,
        i: Value,
        shape: u64,
    ) -> Result<Value, String> {
        let list = self.fb.ins().load(I64, self.trusted, slot, 0);
        let len = self.list_len(list);
        self.bounds(loc, i, len, |t, loc| {
            t.runtime("stilt_rt_list_slot", &[loc, slot, i], true)
                .map(|_| ())
        })?;
        Ok(self.element(list, i, shape, 0))
    }

    /// A pointer to element `i`, in bounds, of the list a slot holds, which nothing else
    /// references, of elements of the shape `shape`: nothing is checked.
    pub(crate) fn list_element_at(&mut self, slot: Value, i: Value, shape: u64) -> Value {
        let list = self.fb.ins().load(I64, self.trusted, slot, 0);
        self.element(list, i, shape, 0)
    }

    /// A pointer to element `i` of `list`, in bounds, if nothing else references the list, and
    /// otherwise what `copy` returns, laid out cold.
    fn unique_element(
        &mut self,
        list: Value,
        i: Value,
        shape: u64,
        copy: impl FnOnce(&mut Self) -> Result<Value, String>,
    ) -> Result<Value, String> {
        self.if_unique(list, |t| t.element(list, i, shape, 0), copy)
    }

    /// Stores the scalar of an operand in the element a pointer points to, in the width of the
    /// shape `shape`.
    pub(crate) fn store_packed(&mut self, args: &[Operand]) -> Result<(), String> {
        let [pointer, x, elem] = args else {
            return Err("a packed store of three operands".to_owned());
        };
        let shape = constant(elem).ok_or("a packed store of a constant shape")?;
        let (p, x) = (self.operand(pointer)?, self.operand(x)?);
        self.store_narrow(p, x, shape);
        Ok(())
    }

    /// Stores the scalar `x` at `addr` in the width of the narrow shape `shape`.
    pub(super) fn store_narrow(&mut self, addr: Value, x: Value, shape: u64) {
        match narrow(shape) {
            Some((I8, _)) => self.fb.ins().istore8(self.trusted, x, addr, 0),
            Some((I16, _)) => self.fb.ins().istore16(self.trusted, x, addr, 0),
            _ => self.fb.ins().istore32(self.trusted, x, addr, 0),
        };
    }
}
