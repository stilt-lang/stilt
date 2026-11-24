//! Calls and returns (`stilt_runtime::abi`): a compiled function returns the words of its
//! result or of its error, then the raised flag, in registers when they fit and otherwise
//! through memory that its caller passes a pointer to; a native returns two words, its result's
//! or its result and the raised flag.

use cranelift_codegen::ir::{InstBuilder, Value, condcodes::IntCC, types::I64};
use stilt_mir::mir::{Arg, BlockId, Callee, Local, MEMORY_WORDS, Operand, offsets};

use crate::arrays::as_i64;
use crate::module::{in_memory, owned_args, params_in_memory, signature};
use crate::translate::Translator;

/// Where a call goes on: the locals its result goes to, the block after it, and for a call that
/// can raise, the locals its error goes to and the block that takes it.
pub(crate) type Then<'a> = (&'a [Local], BlockId, Option<&'a (Vec<Local>, BlockId)>);

impl Translator<'_, '_> {
    /// Returns, or raises if `raise`, the words of a value, the unused words of the function's
    /// results being 0: an array held in memory copied whole to the memory of the results, or
    /// its words loaded into the registers of the results when they fit.
    pub(crate) fn return_words(&mut self, os: &[Operand], raise: bool) -> Result<(), String> {
        let flag = self.fb.ins().iconst(I64, i64::from(raise));
        let results = self.f.results as usize;
        let Some(memory) = self.results else {
            let mut words = Vec::with_capacity(results + 1);
            for o in os {
                let v = self.operand(o)?;
                match self.array_operand(o) {
                    Some(e) => words.extend((0..e.words()).map(|k| {
                        let offset = i32::try_from(8 * k).unwrap_or(0);
                        self.fb.ins().load(I64, self.trusted, v, offset)
                    })),
                    None => words.push(v),
                }
            }
            let zero = self.fb.ins().iconst(I64, 0);
            words.resize(results, zero);
            words.push(flag);
            self.guard_return()?;
            self.fb.ins().return_(&words);
            return Ok(());
        };
        let (at, used) = self.operand_offsets(os);
        for (o, &i) in os.iter().zip(&at) {
            let offset = i32::try_from(8 * i).map_err(|e| e.to_string())?;
            let w = self.operand(o)?;
            if let Some(e) = self.array_operand(o) {
                let to = self.fb.ins().iadd_imm_s(memory, 8 * as_i64(i)?);
                self.copy_words(to, w, e.words())?;
            } else {
                self.fb.ins().store(self.trusted, w, memory, offset);
            }
        }
        self.clear_rest(memory, used, results)?;
        self.guard_return()?;
        self.fb.ins().return_(&[flag]);
        Ok(())
    }

    /// Sets words `from..to` of the memory of a function's results to 0.
    fn clear_rest(&mut self, memory: Value, from: usize, to: usize) -> Result<(), String> {
        if to.saturating_sub(from) > MEMORY_WORDS {
            let at = self.fb.ins().iadd_imm_s(memory, 8 * as_i64(from)?);
            return self.zero_words(at, to - from);
        }
        let zero = self.fb.ins().iconst(I64, 0);
        for i in from..to {
            let offset = i32::try_from(8 * i).map_err(|e| e.to_string())?;
            self.fb.ins().store(self.trusted, zero, memory, offset);
        }
        Ok(())
    }

    pub(crate) fn call(&mut self, callee: &Callee, args: &[Arg], then: Then) -> Result<(), String> {
        if let Callee::Direct(stilt_mir::FnRef::Foreign(c)) = callee {
            return self.call_foreign(c, args, then);
        }
        let (dest, next, raised) = then;
        let mut values = Vec::with_capacity(args.len() + 1);
        let mut rest = args.iter();
        if let Some(Arg::Borrow(loc)) = rest.next() {
            values.push(self.operand(loc)?);
        }
        let code = match callee {
            Callee::Direct(_) => None,
            Callee::Value(closure) => {
                let c = self.operand(closure)?;
                values.push(c);
                Some(self.code_at(c, 0))
            }
            Callee::Method(dict, index) => {
                let d = self.operand(dict)?;
                values.push(d);
                Some(self.code_at(d, *index))
            }
        };
        let params = values.len() + rest.len();
        let values = self.passed(values, rest.as_slice())?;
        let code = match (callee, code) {
            (Callee::Direct(f), _) if self.reg.compiled(f) => {
                Some(self.slot_code(f, &owned_args(args))?)
            }
            (_, code) => code,
        };
        let Some(code) = code else {
            let Callee::Direct(f) = callee else {
                unreachable!("an indirect call has code")
            };
            return self.call_native(f, (&values, args), dest, next, raised);
        };
        let words = self
            .words_of_locals(dest)
            .max(raised.map_or(0, |(e, _)| self.words_of_locals(e)));
        let (results, flag) = self.call_code(code, (values, params), words);
        self.returned(&results, Some(flag), dest, next, raised)
    }

    /// The words a call passes: `values`, then the words of `rest`, each computed. Past the
    /// most parameters, each word goes to memory as it is computed, so that no more than one of
    /// them is live at a time (`crate::module`), and the call passes the memory's address.
    fn passed(&mut self, mut values: Vec<Value>, rest: &[Arg]) -> Result<Vec<Value>, String> {
        let params = values.len() + rest.len();
        let memory = params_in_memory(params).then(|| self.words_slot(params));
        if let Some(slot) = memory {
            for (i, v) in values.iter().enumerate() {
                self.fb.ins().stack_store(I64, *v, slot, slot_offset(i));
            }
        }
        for (i, a) in rest.iter().enumerate() {
            let v = match a {
                Arg::Borrow(o) | Arg::Own(o) | Arg::Ref(o) => self.operand(o)?,
                Arg::Lend(words) => self.lent(words)?,
            };
            match memory {
                Some(slot) => {
                    let at = slot_offset(values.len() + i);
                    self.fb.ins().stack_store(I64, v, slot, at);
                }
                None => values.push(v),
            }
        }
        if let Some(slot) = memory {
            values = vec![self.fb.ins().stack_addr(I64, slot, 0)];
        }
        Ok(values)
    }

    /// Calls compiled code that takes `params` words, as `values` passes them, and returns
    /// `words` words and the raised flag, and returns them: in registers, or in memory.
    fn call_code(
        &mut self,
        code: Value,
        (mut values, params): (Vec<Value>, usize),
        words: usize,
    ) -> (Results, Value) {
        let memory = in_memory(self.module, words).then(|| {
            let slot = self.words_slot(words);
            self.fb.ins().stack_addr(I64, slot, 0)
        });
        values.extend(memory);
        let sig = signature(self.module, params, words);
        let sig = self.fb.import_signature(sig);
        let inst = self.fb.ins().call_indirect(sig, code, &values);
        let results = self.fb.inst_results(inst).to_vec();
        let Some(memory) = memory else {
            let (words, flag) = results.split_at(words);
            return (Results::Registers(words.to_vec()), flag[0]);
        };
        (Results::Memory(memory), results[0])
    }

    /// Calls the native `f`, or computes it inline, and goes on. A native returns two words:
    /// its result and the raised flag when it can raise, and otherwise its result's words.
    fn call_native(
        &mut self,
        f: &stilt_mir::FnRef,
        (values, args): (&[Value], &[Arg]),
        dest: &[Local],
        next: BlockId,
        raised: Option<&(Vec<Local>, BlockId)>,
    ) -> Result<(), String> {
        if let Some(results) = self.inline_native(f, values, args)? {
            return self.returned(&Results::Registers(results), None, dest, next, raised);
        }
        let id = self.native(f, values.len())?;
        let r = self.func_ref(id);
        let inst = self.fb.ins().call(r, values);
        let results = self.fb.inst_results(inst).to_vec();
        if raised.is_some() {
            let words = Results::Registers(results[..1].to_vec());
            self.returned(&words, Some(results[1]), dest, next, raised)
        } else {
            self.returned(&Results::Registers(results), None, dest, next, raised)
        }
    }

    /// Goes on after a call that returned the words `words`, and the raised flag `flag` if it
    /// can raise: to `next` with the result in `dest`, or when it raised, to the raised edge
    /// with the error in its locals.
    pub(crate) fn returned(
        &mut self,
        words: &Results,
        flag: Option<Value>,
        dest: &[Local],
        next: BlockId,
        raised: Option<&(Vec<Local>, BlockId)>,
    ) -> Result<(), String> {
        let next = self.block(next);
        if let (Some((error, block)), Some(flag)) = (raised, flag) {
            let (ok, failed) = (self.fb.create_block(), self.fb.create_block());
            let raised = self.fb.ins().icmp_imm_s(IntCC::NotEqual, flag, 0);
            self.fb.ins().brif(raised, failed, &[], ok, &[]);
            self.fb.switch_to_block(ok);
            self.give(words, dest)?;
            self.fb.ins().jump(next, &[]);
            self.fb.switch_to_block(failed);
            self.give(words, error)?;
            let target = self.block(*block);
            self.fb.ins().jump(target, &[]);
        } else {
            self.give(words, dest)?;
            self.fb.ins().jump(next, &[]);
        }
        Ok(())
    }

    /// Gives `locals` the words a call returned, one after the other: an array held in memory
    /// its words, copied from the memory of the results.
    fn give(&mut self, words: &Results, locals: &[Local]) -> Result<(), String> {
        match words {
            Results::Registers(words) => {
                let mut words = words.iter().copied();
                for &l in locals {
                    let Some(e) = self.array_of(l) else {
                        if let Some(w) = words.next() {
                            self.def_local(l, w)?;
                        }
                        continue;
                    };
                    let to = self.slot_addr(l);
                    for (k, w) in words.by_ref().take(e.words()).enumerate() {
                        let offset = i32::try_from(8 * k).map_err(|e| e.to_string())?;
                        self.fb.ins().store(self.trusted, w, to, offset);
                    }
                }
            }
            Results::Memory(memory) => {
                let (at, _) = offsets(locals.iter().map(|&l| self.repr(l)));
                for (&l, i) in locals.iter().zip(at) {
                    let w = if self.array_of(l).is_some() {
                        self.fb.ins().iadd_imm_s(*memory, 8 * as_i64(i)?)
                    } else {
                        let offset = i32::try_from(8 * i).map_err(|e| e.to_string())?;
                        self.fb.ins().load(I64, self.trusted, *memory, offset)
                    };
                    self.def_local(l, w)?;
                }
            }
        }
        Ok(())
    }
}

/// The words a call returned: in registers, or in memory, where this address points.
pub(crate) enum Results {
    Registers(Vec<Value>),
    Memory(Value),
}

/// The offset of word `i` of memory that holds words one after the other.
fn slot_offset(i: usize) -> i32 {
    i32::try_from(8 * i).expect("a slot under 2 GiB")
}
