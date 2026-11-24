//! What a compiled program declares: its functions, the natives and runtime functions it
//! imports, its static data, and a slot for the value of each constant.

mod asked;
mod data;
mod guard;

use std::collections::HashSet;
use std::sync::Arc;

use cranelift_codegen::ir::{AbiParam, Signature, Type, types::I64};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use rustc_hash::FxHashMap as HashMap;
use stilt_mir::FnRef;
use stilt_mir::mir::{Arg, Const, Function, ParamMode, Repr};

pub(crate) use asked::{Answer, Asked, Known, known};

/// The layout of objects, as `stilt-runtime` defines it.
pub(crate) const HEADER: u32 = 16;

/// The number of words the target returns in registers: the integer registers Cranelift
/// returns values in, eight on aarch64 and two on x86-64.
fn return_registers(module: &dyn Module) -> usize {
    if module.isa().name() == "aarch64" {
        8
    } else {
        2
    }
}

/// Whether a function that returns `results` words returns them in memory: when they and the
/// raised flag don't fit in the target's registers.
pub(crate) fn in_memory(module: &dyn Module, results: usize) -> bool {
    results + 1 > return_registers(module)
}

/// The most words a compiled function takes as parameters of its own. A function that takes
/// more, as one that takes a large array does (generics.large-arrays), takes a pointer to memory
/// that holds them, which its caller fills.
pub(crate) const MOST_PARAMS: usize = 256;

/// Whether a function that takes `params` words takes them in memory.
pub(crate) fn params_in_memory(params: usize) -> bool {
    params > MOST_PARAMS
}

/// The signature of a compiled function: `params` words in, and `results` words and a raised
/// flag out (`stilt_runtime::abi`). Words that don't fit in registers with the flag go to
/// memory that the caller passes a pointer to, after the parameters, and only the flag comes
/// back. More than [`MOST_PARAMS`] parameters come in memory too, through one pointer.
pub(crate) fn signature(module: &dyn Module, params: usize, results: usize) -> Signature {
    let mut sig = module.make_signature();
    let params = if params_in_memory(params) { 1 } else { params };
    sig.params
        .extend(std::iter::repeat_n(AbiParam::new(I64), params));
    if in_memory(module, results) {
        sig.params.push(AbiParam::new(I64));
        sig.returns.push(AbiParam::new(I64));
    } else {
        sig.returns
            .extend(std::iter::repeat_n(AbiParam::new(I64), results + 1));
    }
    sig
}

/// The signature of a runtime function: `params` words in, and one word out if it returns.
pub(crate) fn runtime_signature(module: &dyn Module, params: usize, returns: bool) -> Signature {
    let words = vec![I64; params];
    typed_signature(module, &words, if returns { &[I64] } else { &[] })
}

/// The signature of a runtime function that takes values of the types `params` and returns
/// values of the types `returns`, each in a register of its class.
pub(crate) fn typed_signature(module: &dyn Module, params: &[Type], returns: &[Type]) -> Signature {
    let mut sig = module.make_signature();
    sig.params.extend(params.iter().map(|&t| AbiParam::new(t)));
    sig.returns
        .extend(returns.iter().map(|&t| AbiParam::new(t)));
    sig
}

/// The runtime's name for a native of the standard library.
pub(crate) fn native_symbol(f: &FnRef) -> Option<String> {
    let flat = |home: &str| home.replace('.', "_");
    match f {
        FnRef::Function(item) => Some(format!("stilt_{}_{}", flat(&item.home), item.name)),
        FnRef::Member(owner, name) => {
            Some(format!("stilt_{}_{}_{name}", flat(&owner.home), owner.name))
        }
        _ => None,
    }
}

/// The positions of the parameters a function owns.
pub(crate) fn owned_params(f: &Function) -> Vec<usize> {
    f.params
        .iter()
        .enumerate()
        .filter(|(_, p)| p.mode == ParamMode::Owned)
        .map(|(i, _)| i)
        .collect()
}

/// The positions of the arguments a direct call gives its callee, which are those of the
/// parameters the callee owns.
pub(crate) fn owned_args(args: &[Arg]) -> Vec<usize> {
    args.iter()
        .enumerate()
        .filter(|(_, a)| matches!(a, Arg::Own(_)))
        .map(|(i, _)| i)
        .collect()
}

/// The symbol of a function's code, of letters, digits and underscores, which every object
/// format and linker takes, before its number makes it unique.
pub(crate) fn readable(f: &FnRef) -> String {
    (f.symbol().chars())
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

/// The symbol `prefix`, then `n` in decimal, then each of `rest`: as `format!` writes it, without
/// its machinery, since a build names each of its functions and objects anew (goal
/// compile-time-code-rebuilds).
fn numbered(prefix: &str, n: u32, rest: &[&str]) -> String {
    let mut name =
        String::with_capacity(prefix.len() + 10 + rest.iter().map(|r| r.len()).sum::<usize>());
    name.push_str(prefix);
    push_decimal(&mut name, n);
    for r in rest {
        name.push_str(r);
    }
    name
}

fn push_decimal(s: &mut String, n: u32) {
    if n >= 10 {
        push_decimal(s, n / 10);
    }
    s.extend(char::from_digit(n % 10, 10));
}

/// The names of a program's functions and data in its module.
///
/// Every compiled function has a *slot* for each calling convention it has had: a word that holds
/// the address of its code. Calls, function values and dictionaries all reach a function through
/// its slot, so a new version of it takes effect when its address is stored there. Function values
/// and dictionaries reach code that owns no parameter. A version that owns other parameters than
/// the last gets a slot of its own: code already running passes its arguments in the old
/// convention, so it goes on calling the version that takes them so, while the callers patched with
/// the new version call it.
pub(crate) struct Registry {
    /// The slot of each compiled function in each of its conventions, each the positions of
    /// the parameters it owns, those it consumes (`stilt-rc`).
    slots: HashMap<FnRef, Vec<(Vec<usize>, DataId)>>,
    /// The code of each function's latest version, and the number of versions it has had.
    pub(crate) code: HashMap<FnRef, (FuncId, u32)>,
    pub(crate) imports: HashMap<String, FuncId>,
    data: HashMap<Const, DataId>,
    /// The slot of each constant's value, its representation, and its code.
    pub(crate) constants: Vec<(FnRef, DataId, Box<[Repr]>)>,
    pub(crate) available: Arc<HashSet<&'static str>>,
    /// The conventions of each function that the module compiles, for a registry that
    /// translates a function apart, into a draft of the module, and declares the slots it
    /// reaches as it reaches them ([`crate::draft`]).
    known: Option<Arc<Known>>,
    next_data: u32,
    /// Whether compiled code polls the runtime's stop flag, as a watched run's must.
    pub(crate) watched: bool,
    stop: Option<DataId>,
    /// Whether the code goes into an object file, whose slots hold their functions' addresses
    /// from the start, rather than into memory, where they are set once the code is there.
    pub(crate) object: bool,
    /// Whether compilation keeps what debuggers need of each function (goal debuggable-builds).
    pub(crate) debug: bool,
    next_function: u32,
    /// What translating a function has asked so far, with each answer, when it is recorded,
    /// so that a later build that reuses the function's code asks it again ([`crate::reuse`]).
    pub(crate) asked: Option<Vec<(Asked, Answer)>>,
    /// The functions that the check of `without alloc` guards ([`crate::guards`]).
    pub(crate) guards: Arc<stilt_mir::Guards>,
}

impl Registry {
    pub(crate) fn new(available: HashSet<&'static str>) -> Self {
        Self {
            slots: HashMap::default(),
            code: HashMap::default(),
            imports: HashMap::default(),
            data: HashMap::default(),
            constants: Vec::new(),
            available: Arc::new(available),
            known: None,
            next_data: 0,
            watched: false,
            stop: None,
            object: false,
            debug: true,
            next_function: 0,
            asked: None,
            guards: Arc::default(),
        }
    }

    /// Makes room for the declarations of `functions` functions and `data` objects of static
    /// data, as many as the last build of the program declared, so that its maps grow once.
    pub(crate) fn reserve(&mut self, functions: usize, data: usize) {
        self.code.reserve(functions);
        self.slots.reserve(functions);
        self.data.reserve(data);
    }

    /// How many objects of static data it declared for constants.
    pub(crate) fn data_count(&self) -> usize {
        self.data.len()
    }

    /// Records what translation asked, and the answer, while it is recorded.
    fn ask(&mut self, asked: impl FnOnce() -> Asked, answer: Answer) {
        if let Some(record) = self.asked.as_mut() {
            record.push((asked(), answer));
        }
    }

    /// The runtime's stop flag, which a watched run polls.
    pub(crate) fn stop_flag(&mut self, module: &mut dyn Module) -> Result<DataId, String> {
        let id = match self.stop {
            Some(id) => id,
            None => module
                .declare_data("stilt_rt_stop", Linkage::Import, true, false)
                .map_err(|e| format!("cannot import the stop flag: {e}"))?,
        };
        self.stop = Some(id);
        self.ask(|| Asked::Stop, Answer::Data(id));
        Ok(id)
    }

    /// Declares a new version of a compiled function, and its slot in the version's convention
    /// if it has none yet.
    pub(crate) fn declare(
        &mut self,
        module: &mut dyn Module,
        function: &Function,
    ) -> Result<FuncId, String> {
        self.declare_as(module, function, &readable(&function.name))
    }

    /// As [`Registry::declare`], under the symbol that [`readable`] gives the function.
    pub(crate) fn declare_as(
        &mut self,
        module: &mut dyn Module,
        function: &Function,
        readable: &str,
    ) -> Result<FuncId, String> {
        let f = &function.name;
        let version = self.code.get(f).map_or(0, |&(_, v)| v + 1);
        let id = self.declare_code(module, function, readable, "")?;
        self.code.insert(f.clone(), (id, version));
        let owned = owned_params(function);
        if self.slot_id(f, &owned).is_none() {
            let slot = self.fresh_data(module, true)?;
            let mut desc = DataDescription::new();
            desc.set_align(8);
            if self.object {
                desc.define(vec![0; 8].into_boxed_slice());
                let code = module.declare_func_in_data(id, &mut desc);
                desc.write_function_addr(0, code);
            } else {
                desc.define_zeroinit(8);
            }
            module.define_data(slot, &desc).map_err(|e| e.to_string())?;
            self.slots.entry(f.clone()).or_default().push((owned, slot));
        }
        Ok(id)
    }

    /// Declares a bridge to a function from one of its earlier conventions (`crate::bridge`).
    pub(crate) fn declare_bridge(
        &mut self,
        module: &mut dyn Module,
        bridge: &Function,
    ) -> Result<FuncId, String> {
        self.declare_code(module, bridge, &readable(&bridge.name), "_bridge")
    }

    /// Declares code for `function`, under its readable symbol, made unique by its number.
    fn declare_code(
        &mut self,
        module: &mut dyn Module,
        function: &Function,
        readable: &str,
        suffix: &str,
    ) -> Result<FuncId, String> {
        let name = numbered("stilt_", self.next_function, &["_", readable, suffix]);
        self.next_function += 1;
        let sig = signature(module, function.params.len(), function.results as usize);
        module
            .declare_function(&name, Linkage::Local, &sig)
            .map_err(|e| format!("cannot declare {name}: {e}"))
    }

    /// The conventions a function has had slots for, each as the positions of the parameters
    /// it owns.
    pub(crate) fn conventions(&self, f: &FnRef) -> Vec<Vec<usize>> {
        let slots = self.slots.get(f).into_iter().flatten();
        slots.map(|(owned, _)| owned.clone()).collect()
    }

    /// Whether a function is compiled, rather than a native of the runtime.
    pub(crate) fn compiled(&mut self, f: &FnRef) -> bool {
        let compiled =
            self.code.contains_key(f) || self.known.as_ref().is_some_and(|k| k.contains_key(f));
        self.ask(|| Asked::Compiled(f.clone(), compiled), Answer::None);
        compiled
    }

    /// The slot of a compiled function in the convention that owns the parameters at `owned`.
    pub(crate) fn slot(
        &mut self,
        module: &mut dyn Module,
        f: &FnRef,
        owned: &[usize],
    ) -> Result<DataId, String> {
        let id = self.slot_in(module, f, owned)?;
        self.ask(|| Asked::Slot(f.clone(), owned.to_vec()), Answer::Data(id));
        Ok(id)
    }

    /// As [`Registry::slot`], unrecorded: in a draft, a slot that the module declares is
    /// declared in the draft once reached.
    fn slot_in(
        &mut self,
        module: &mut dyn Module,
        f: &FnRef,
        owned: &[usize],
    ) -> Result<DataId, String> {
        if let Some(id) = self.slot_id(f, owned) {
            return Ok(id);
        }
        let known = self.known.as_ref();
        if !known.is_some_and(|k| k.get(f).is_some_and(|c| c.iter().any(|o| o == owned))) {
            return self.slot_of(f, owned);
        }
        let id = self.fresh_data(module, true)?;
        self.slots
            .entry(f.clone())
            .or_default()
            .push((owned.to_vec(), id));
        Ok(id)
    }

    /// As [`Registry::slot`], unrecorded.
    pub(crate) fn slot_of(&self, f: &FnRef, owned: &[usize]) -> Result<DataId, String> {
        self.slot_id(f, owned)
            .ok_or_else(|| format!("no code for {f} owning the parameters {owned:?}"))
    }

    fn slot_id(&self, f: &FnRef, owned: &[usize]) -> Option<DataId> {
        let mut slots = self.slots.get(f).into_iter().flatten();
        slots.find(|(o, _)| o == owned).map(|&(_, id)| id)
    }

    /// The function the runtime defines under `name`, with this signature.
    pub(crate) fn import(
        &mut self,
        module: &mut dyn Module,
        name: &str,
        sig: &Signature,
    ) -> Result<FuncId, String> {
        let id = self.import_of(module, name, sig)?;
        self.ask(
            || Asked::Import(name.to_owned(), sig.clone()),
            Answer::Function(id),
        );
        Ok(id)
    }

    /// A foreign function that an object imports by its name, from the target's C library or a
    /// library the program links (c.build-targets), with C's signature `sig`.
    pub(crate) fn foreign(
        &mut self,
        module: &mut dyn Module,
        name: &str,
        sig: &Signature,
    ) -> Result<FuncId, String> {
        let id = if let Some(&id) = self.imports.get(name) {
            id
        } else {
            let id = module
                .declare_function(name, Linkage::Import, sig)
                .map_err(|e| format!("cannot import {name}: {e}"))?;
            self.imports.insert(name.to_owned(), id);
            id
        };
        self.ask(
            || Asked::Foreign(name.to_owned(), sig.clone()),
            Answer::Function(id),
        );
        Ok(id)
    }

    fn import_of(
        &mut self,
        module: &mut dyn Module,
        name: &str,
        sig: &Signature,
    ) -> Result<FuncId, String> {
        if let Some(&id) = self.imports.get(name) {
            return Ok(id);
        }
        if !self.available.contains(name) {
            return Err(format!("the runtime has no function `{name}`"));
        }
        let id = module
            .declare_function(name, Linkage::Import, sig)
            .map_err(|e| format!("cannot import {name}: {e}"))?;
        self.imports.insert(name.to_owned(), id);
        Ok(id)
    }

    /// The cell of a constant's value, of the words `words`: whether it is computed, then its
    /// words. An edit that changes the constant's layout gives it a new cell.
    pub(crate) fn constant(
        &mut self,
        module: &mut dyn Module,
        f: &FnRef,
        words: &[Repr],
    ) -> Result<DataId, String> {
        let id = self.constant_of(module, f, words)?;
        self.ask(
            || Asked::Constant(f.clone(), words.into()),
            Answer::Data(id),
        );
        Ok(id)
    }

    fn constant_of(
        &mut self,
        module: &mut dyn Module,
        f: &FnRef,
        words: &[Repr],
    ) -> Result<DataId, String> {
        if let Some((_, id, _)) = self
            .constants
            .iter()
            .find(|(g, _, w)| g == f && **w == *words)
        {
            return Ok(*id);
        }
        let id = self.fresh_data(module, true)?;
        let mut desc = DataDescription::new();
        desc.define_zeroinit(8 + 8 * stilt_mir::mir::offsets(words.iter().copied()).1);
        desc.set_align(8);
        module.define_data(id, &desc).map_err(|e| e.to_string())?;
        self.constants.push((f.clone(), id, words.into()));
        Ok(id)
    }

    pub(crate) fn fresh_data(
        &mut self,
        module: &mut dyn Module,
        writable: bool,
    ) -> Result<DataId, String> {
        let name = numbered("stilt_data_", self.next_data, &[]);
        self.next_data += 1;
        module
            .declare_data(&name, Linkage::Local, writable, false)
            .map_err(|e| format!("cannot declare {name}: {e}"))
    }

    /// The cells of every constant declared so far, as the entry releases them.
    pub(crate) fn constants(&mut self) -> Vec<(FnRef, DataId, Box<[Repr]>)> {
        let cells = self.constants.clone();
        let asked = || {
            Asked::Constants(
                cells
                    .iter()
                    .map(|(f, _, w)| (f.clone(), w.clone()))
                    .collect(),
            )
        };
        self.ask(asked, Answer::None);
        cells
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn a_numbered_symbol_is_the_one_format_writes() {
        for n in [0, 7, 10, 99, 1778, u32::MAX] {
            let name = super::numbered("stilt_", n, &["_", "main_f", "_bridge"]);
            assert_eq!(name, format!("stilt_{n}_main_f_bridge"));
        }
        assert_eq!(super::numbered("stilt_data_", 305, &[]), "stilt_data_305");
    }
}
