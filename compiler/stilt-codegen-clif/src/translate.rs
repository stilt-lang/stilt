//! Translating one MIR function to Cranelift: its locals become variables, or stack slots for
//! those a pointer is taken to ([`crate::locals`]), and its blocks Cranelift blocks.

use std::collections::HashMap;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{
    Block, FuncRef, Inst, InstBuilder, MemFlagsData, Signature, SourceLoc, StackSlot, TrapCode,
    Type, Value, ValueLabel, types::I64,
};
use cranelift_frontend::{FunctionBuilder, Switch, Variable};
use cranelift_module::{FuncId, Module};
use stilt_mir::mir::{BlockId, Const, Function, Local, Operand, Repr, Stmt, Terminator};

use crate::module::{HEADER, Registry, runtime_signature, signature};

pub(crate) struct Translator<'a, 'b> {
    pub(crate) fb: FunctionBuilder<'b>,
    pub(crate) module: &'a mut dyn Module,
    pub(crate) reg: &'a mut Registry,
    pub(crate) f: &'a Function,
    /// The type of each local's values ([`crate::floats`]).
    pub(crate) types: Vec<Type>,
    pub(crate) vars: Vec<Variable>,
    /// The slot of each local that lives in memory, and its offset there.
    pub(crate) slots: HashMap<Local, (StackSlot, i32)>,
    /// Where the function stores the words it returns, when they go to memory.
    pub(crate) results: Option<Value>,
    blocks: Vec<Block>,
    /// The index of the MIR block being translated.
    current: usize,
    /// Whether the MIR block being translated raises.
    pub(crate) raising: bool,
    funcs: HashMap<FuncId, FuncRef>,
    /// The flags of loads and stores of words the compiler knows are aligned and valid.
    pub(crate) trusted: MemFlagsData,
    /// The flags of a bitcast.
    pub(crate) plain: MemFlagsData,
    /// The location words of the function's source locations, by their numbers.
    locs: Vec<u64>,
    /// Each value that a named local takes, with the local's label.
    pub(crate) labels: Vec<(Value, ValueLabel)>,
    /// What the function does about the check of `without alloc` ([`crate::guards`]).
    pub(crate) guard: Option<stilt_mir::Guard>,
    /// The count of limited frames that a function that allocates found on entry.
    pub(crate) saved_count: Option<Value>,
}

/// What debuggers need of a translated function, by the numbers and the labels its IR marks.
pub(crate) struct Labels {
    /// The location words of its source locations, by their numbers.
    pub(crate) locs: Vec<u64>,
    /// Each value that a named local takes, with the local's label.
    pub(crate) values: Vec<(Value, ValueLabel)>,
    /// The slot of each named array held in memory, and its offset there.
    pub(crate) arrays: Vec<(Local, StackSlot, i32)>,
}

/// The trap of code that can't be reached.
pub(crate) const UNREACHABLE: TrapCode = TrapCode::unwrap_user(1);

impl<'a, 'b> Translator<'a, 'b> {
    pub(crate) fn new(
        fb: FunctionBuilder<'b>,
        module: &'a mut dyn Module,
        reg: &'a mut Registry,
        f: &'a Function,
    ) -> Self {
        Self {
            trusted: MemFlagsData::trusted(),
            plain: MemFlagsData::new(),
            fb,
            module,
            reg,
            f,
            types: crate::floats::local_types(f),
            vars: Vec::new(),
            slots: HashMap::new(),
            results: None,
            blocks: Vec::new(),
            current: 0,
            raising: false,
            funcs: HashMap::new(),
            locs: Vec::new(),
            labels: Vec::new(),
            guard: None,
            saved_count: None,
        }
    }

    /// Ends the translation, and returns what debuggers need of the function: the location
    /// words of its source locations, by their numbers, each value a named local takes, with
    /// its label, and the slot of each named array held in memory, with its offset there.
    pub(crate) fn finish(self, config: cranelift_codegen::isa::TargetFrontendConfig) -> Labels {
        let named = |l: &Local| self.f.locals[l.0 as usize].shown.is_some();
        let mut arrays: Vec<(Local, StackSlot, i32)> = self
            .slots
            .iter()
            .filter(|(l, _)| named(l) && self.array_of(**l).is_some())
            .map(|(&l, &(slot, offset))| (l, slot, offset))
            .collect();
        arrays.sort_unstable_by_key(|&(l, ..)| l);
        self.fb.finalize(config);
        Labels {
            locs: self.locs,
            values: self.labels,
            arrays,
        }
    }

    /// Gives the code that follows the source location of the location word `word`.
    fn source_at(&mut self, word: u64) {
        let number = self
            .locs
            .iter()
            .position(|&w| w == word)
            .unwrap_or_else(|| {
                self.locs.push(word);
                self.locs.len() - 1
            });
        self.fb
            .set_srcloc(SourceLoc::new(u32::try_from(number).unwrap_or(0)));
    }

    /// Translates the whole function.
    pub(crate) fn run(&mut self) -> Result<(), String> {
        let entry = self.fb.create_block();
        self.fb.append_block_params_for_function_params(entry);
        self.fb.switch_to_block(entry);
        self.declare_locals()?;
        let params: Vec<Value> = self.fb.block_params(entry).to_vec();
        let n = self.f.params.len();
        // Parameters past the most a function takes come in memory (`crate::module`), each
        // word loaded where its local takes it.
        if crate::module::params_in_memory(n) {
            for (i, p) in self.f.params.iter().enumerate() {
                let offset = i32::try_from(8 * i).expect("a slot under 2 GiB");
                let v = self.fb.ins().load(I64, self.trusted, params[0], offset);
                self.def_local(p.local, v)?;
            }
            self.results = params.get(1).copied();
        } else {
            for (p, &v) in self.f.params.iter().zip(&params) {
                self.def_local(p.local, v)?;
            }
            self.results = params.get(n).copied();
        }
        self.poll()?;
        self.guard_entry()?;
        self.blocks = (0..self.f.blocks.len())
            .map(|_| self.fb.create_block())
            .collect();
        let first = self.blocks[0];
        self.fb.ins().jump(first, &[]);
        for (i, block) in self.f.blocks.iter().enumerate() {
            self.current = i;
            self.raising = matches!(block.term, Terminator::Raise(_));
            // A block that ends the program is a failure path ([`crate::cold`]).
            if matches!(
                block.term,
                Terminator::Panic { .. } | Terminator::Unreachable
            ) {
                self.fb.set_cold_block(self.blocks[i]);
            }
            self.fb.switch_to_block(self.blocks[i]);
            for stmt in &block.stmts {
                self.stmt(stmt)?;
            }
            self.term(&block.term)?;
        }
        self.fb.seal_all_blocks();
        Ok(())
    }

    pub(crate) fn func_ref(&mut self, id: FuncId) -> FuncRef {
        if let Some(&r) = self.funcs.get(&id) {
            return r;
        }
        let r = self.module.declare_func_in_func(id, self.fb.func);
        self.funcs.insert(id, r);
        r
    }

    /// The value of an operand, as a word.
    pub(crate) fn operand(&mut self, o: &Operand) -> Result<Value, String> {
        Ok(match o {
            Operand::Local(l) => {
                let v = self.use_local(*l);
                self.local_word(*l, v)
            }
            Operand::Const(Const::Word(w)) => self.fb.ins().iconst(I64, w.cast_signed()),
            Operand::Const(Const::Code(f)) => {
                let slot = self.reg.slot(self.module, f, &[])?;
                let gv = self.module.declare_data_in_func(slot, self.fb.func);
                self.fb.ins().symbol_value(I64, gv)
            }
            Operand::Const(c) => {
                let id = self.reg.data(self.module, c)?;
                let gv = self.module.declare_data_in_func(id, self.fb.func);
                self.fb.ins().symbol_value(I64, gv)
            }
        })
    }

    /// Calls a function of the runtime.
    pub(crate) fn runtime(
        &mut self,
        name: &str,
        args: &[Value],
        returns: bool,
    ) -> Result<Option<Value>, String> {
        let sig = runtime_signature(self.module, args.len(), returns);
        let call = self.call_runtime(name, &sig, args)?;
        Ok(self.fb.inst_results(call).first().copied())
    }

    /// Calls the runtime's function `name`, whose signature is `sig`.
    pub(crate) fn call_runtime(
        &mut self,
        name: &str,
        sig: &Signature,
        args: &[Value],
    ) -> Result<Inst, String> {
        let id = self.reg.import(self.module, name, sig)?;
        let r = self.func_ref(id);
        Ok(self.fb.ins().call(r, args))
    }

    /// In a watched run, ends the run when the runtime's stop flag is set. The call that ends
    /// it is laid out cold, after the rest of the function, as a failure path is, so that the
    /// hot path pays only the flag's load and a branch not taken.
    fn poll(&mut self) -> Result<(), String> {
        if !self.reg.watched {
            return Ok(());
        }
        let flag = self.reg.stop_flag(self.module)?;
        let gv = self.module.declare_data_in_func(flag, self.fb.func);
        let addr = self.fb.ins().symbol_value(I64, gv);
        let stop = self.fb.ins().load(I64, self.plain, addr, 0);
        let (stopping, go_on) = (self.fb.create_block(), self.fb.create_block());
        self.fb.set_cold_block(stopping);
        self.fb.ins().brif(stop, stopping, &[], go_on, &[]);
        self.fb.switch_to_block(stopping);
        // The flag can be cleared before the call reads it, when a stop times out, and the run
        // then goes on.
        self.runtime("stilt_rt_poll", &[], false)?;
        self.fb.ins().jump(go_on, &[]);
        self.fb.switch_to_block(go_on);
        Ok(())
    }

    /// Runs `f` only when `cond` is nonzero.
    pub(crate) fn when(
        &mut self,
        cond: Value,
        f: impl FnOnce(&mut Self) -> Result<(), String>,
    ) -> Result<(), String> {
        let (then, join) = (self.fb.create_block(), self.fb.create_block());
        self.fb.ins().brif(cond, then, &[], join, &[]);
        self.fb.switch_to_block(then);
        f(self)?;
        self.fb.ins().jump(join, &[]);
        self.fb.switch_to_block(join);
        Ok(())
    }

    /// Counts a reference, or releases one, of a word of this representation, or of each
    /// counted word of an array held in memory, whose address `v` is.
    pub(crate) fn count(&mut self, v: Value, repr: Repr, dup: bool) -> Result<(), String> {
        let count = |t: &mut Self| if dup { t.retain(v) } else { t.release(v) };
        match repr {
            Repr::Scalar => Ok(()),
            Repr::Heap => count(self),
            Repr::Generic(w) => {
                let witness = self.use_local(w);
                let heap = self.fb.ins().band_imm_u(witness, 1);
                self.when(heap, count)
            }
            Repr::Array(e) => self.count_array(v, e, dup),
        }
    }

    fn stmt(&mut self, s: &Stmt) -> Result<(), String> {
        match s {
            Stmt::Assign(l, r) => {
                if let Some(e) = self.array_of(*l) {
                    self.assign_array(*l, e, r)?;
                } else {
                    let v = self.rvalue(r, *l)?;
                    self.def_local(*l, v)?;
                }
            }
            Stmt::Store {
                slot,
                value,
                repr: Repr::Array(e),
            } => {
                let p = self.operand(slot)?;
                self.count_array(p, *e, false)?;
                match value {
                    Operand::Local(_) => {
                        let v = self.operand(value)?;
                        self.copy_words(p, v, e.words())?;
                    }
                    Operand::Const(_) => self.zero_words(p, e.words())?,
                }
            }
            Stmt::Store { slot, value, repr } => {
                let p = self.operand(slot)?;
                let v = self.held(value)?;
                let old = self.fb.ins().load(I64, self.trusted, p, 0);
                self.fb.ins().store(self.trusted, v, p, 0);
                self.count(old, *repr, false)?;
            }
            Stmt::Effect(f, args) => self.effect(*f, args)?,
            Stmt::ReleaseConstants => self.release_constants()?,
            Stmt::At(word) => self.source_at(*word),
            // A profiled run's count (builds.profile-use).
            Stmt::Count(counted, word) => {
                let kind = self.fb.ins().iconst(I64, counted.number().cast_signed());
                let at = self.fb.ins().iconst(I64, word.cast_signed());
                self.runtime("stilt_rt_profile_count", &[kind, at], false)?;
            }
            Stmt::Dup(l) | Stmt::Drop(l) => {
                let v = self.use_local(*l);
                self.count(v, self.repr(*l), matches!(s, Stmt::Dup(_)))?;
            }
        }
        Ok(())
    }

    /// Releases the value of every constant that was computed, whose cell's state is 1.
    fn release_constants(&mut self) -> Result<(), String> {
        for (_, id, words) in self.reg.constants() {
            let gv = self.module.declare_data_in_func(id, self.fb.func);
            let addr = self.fb.ins().symbol_value(I64, gv);
            let state = self.fb.ins().load(I64, self.trusted, addr, 0);
            let done = self.fb.ins().icmp_imm_s(IntCC::Equal, state, 1);
            self.when(done, |t| {
                let (at, _) = stilt_mir::mir::offsets(words.iter().copied());
                for (&repr, i) in words.iter().zip(at) {
                    let at = i32::try_from(8 + 8 * i).expect("a constant under 2 GB");
                    let v = match repr {
                        Repr::Array(_) => t.fb.ins().iadd_imm_s(addr, i64::from(at)),
                        _ => t.fb.ins().load(I64, t.trusted, addr, at),
                    };
                    t.count(v, repr, false)?;
                }
                Ok(())
            })?;
        }
        Ok(())
    }

    pub(crate) fn block(&self, b: BlockId) -> Block {
        self.blocks[b.0 as usize]
    }

    fn term(&mut self, t: &Terminator) -> Result<(), String> {
        match t {
            Terminator::Goto(b) => {
                // A jump back is a loop's back edge, where a watched run polls.
                if b.0 as usize <= self.current {
                    self.poll()?;
                }
                let target = self.block(*b);
                self.fb.ins().jump(target, &[]);
            }
            Terminator::Branch {
                cond,
                then,
                otherwise,
            } => {
                let c = self.operand(cond)?;
                let (yes, no) = (self.block(*then), self.block(*otherwise));
                self.fb.ins().brif(c, yes, &[], no, &[]);
            }
            Terminator::Switch {
                value,
                cases,
                otherwise,
            } => {
                let v = self.operand(value)?;
                let mut switch = Switch::new();
                for (k, b) in cases {
                    switch.set_entry(u128::from(*k), self.block(*b));
                }
                let otherwise = self.block(*otherwise);
                switch.emit(&mut self.fb, v, otherwise);
            }
            Terminator::Call {
                callee,
                args,
                dest,
                next,
                raised,
            } => {
                self.call(callee, args, (dest, *next, raised.as_ref()))?;
            }
            Terminator::Return(os) => self.return_words(os, false)?,
            Terminator::Raise(os) => self.return_words(os, true)?,
            Terminator::Panic { kind, detail, loc } => {
                self.panic(*kind, detail.as_ref(), loc)?;
                self.fb.ins().trap(UNREACHABLE);
            }
            Terminator::Unreachable => {
                self.fb.ins().trap(UNREACHABLE);
            }
        }
        Ok(())
    }

    /// The address of field `index` of a data object.
    pub(crate) fn field_addr(&mut self, object: Value, index: u32) -> Value {
        self.fb
            .ins()
            .iadd_imm_s(object, i64::from(HEADER + 8 * index))
    }

    /// The current code of a compiled function in the convention that owns the parameters at
    /// `owned`, from its slot.
    pub(crate) fn slot_code(
        &mut self,
        f: &stilt_mir::FnRef,
        owned: &[usize],
    ) -> Result<Value, String> {
        let slot = self.reg.slot(self.module, f, owned)?;
        let gv = self.module.declare_data_in_func(slot, self.fb.func);
        let addr = self.fb.ins().symbol_value(I64, gv);
        Ok(self.fb.ins().load(I64, self.trusted, addr, 0))
    }

    /// The code that field `index` of a closure or a dictionary reaches: the field holds the
    /// address of a slot.
    pub(crate) fn code_at(&mut self, object: Value, index: u32) -> Value {
        let addr = self.field_addr(object, index);
        let slot = self.fb.ins().load(I64, self.trusted, addr, 0);
        self.fb.ins().load(I64, self.trusted, slot, 0)
    }

    /// The native of the runtime that a direct call to a function without code calls, which
    /// returns two words (`stilt_runtime::abi`).
    pub(crate) fn native(&mut self, f: &stilt_mir::FnRef, params: usize) -> Result<FuncId, String> {
        let name = crate::module::native_symbol(f).ok_or_else(|| format!("no code for {f}"))?;
        let sig = signature(self.module, params, 1);
        self.reg.import(self.module, &name, &sig)
    }
}
