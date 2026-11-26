//! Stilt's debug back end: the MIR of a program compiled by Cranelift into the compiler's own
//! process, where its JIT runs it without linking (goal edit-to-running-program).
//!
//! Every function takes words and returns the words of its result and a raised flag
//! (`stilt_runtime::abi`).
//! The natives of the standard library, and the functions that compiled code calls for what it
//! doesn't do inline, are the runtime's, which the JIT finds by the addresses the runtime
//! lists.
//!
//! An [`Image`] holds a program's compiled code, and takes later versions of it: each function
//! is reached through a slot that holds the address of its code, so a function whose MIR
//! changed is compiled again and its slot set, while the program runs (hot patching). A function
//! has a slot for each calling convention it has had, and the slots of the earlier ones hold
//! bridges to its latest code ([`bridge`]).
//!
//! [`object`] compiles a program into an object file, reusing the machine code of each function
//! that the build before it compiled, which [`Built`] keeps, while the function's code is the
//! same.
//!
//! Its place among the crates (`compiler/README.md`): it depends on `stilt-db`, `stilt-mir` and
//! `stilt-runtime` alone, reading counted MIR and no earlier phase's results.
#![warn(missing_docs)]

mod arrays;
mod bridge;
mod calls;
mod checks;
mod cold;
mod compile;
mod debug;
mod draft;
mod floats;
mod foreign;
mod guards;
mod inline;
mod library;
mod lists;
mod locals;
mod module;
mod object;
mod prim;
mod reuse;
mod rvalue;
mod target;
#[cfg(test)]
mod testing;
mod translate;

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use cranelift_jit::{ArenaMemoryProvider, JITBuilder, JITModule};
use cranelift_module::{FuncId, default_libcall_names};
use stilt_mir::FnRef;
use stilt_mir::mir::Function;

use crate::debug::jit::Registration;
use crate::module::Registry;

pub use crate::library::library;
pub use crate::object::object;
pub use crate::reuse::Built;
pub use crate::target::Target;

/// The address space an image reserves for its code and data: room for every version of the
/// functions that hot patching compiles in a long session of the 100K-line project.
const ARENA: usize = 1 << 30;

/// A program's code in memory, which later versions of its functions replace.
pub struct Image {
    module: Option<JITModule>,
    reg: Registry,
    /// The MIR of each function's version in the image, and its guard.
    loaded: HashMap<FnRef, (Arc<Function>, Option<stilt_mir::Guard>)>,
    /// Where the program's files are, which debuggers read.
    files: Vec<PathBuf>,
    /// The DWARF of each load, as debuggers see it (goal debuggable-builds).
    registrations: Vec<Registration>,
}

impl std::fmt::Debug for Image {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Image")
            .field("functions", &self.loaded.len())
            .finish_non_exhaustive()
    }
}

/// What a load of an image compiled.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Loaded {
    /// The functions compiled, new or changed, in the order given.
    pub compiled: Vec<FnRef>,
    /// How long making the compiled code live took: its memory made executable, its DWARF given to
    /// debuggers and its slots set, which the latency harness reports apart from compiling (goal
    /// edit-to-running-program).
    pub patching: Duration,
}

impl Image {
    /// An empty image, which knows the runtime's functions.
    ///
    /// # Errors
    ///
    /// Fails when Cranelift doesn't support the host.
    pub fn new() -> Result<Self, String> {
        // Debuggers find each frame, and the locals it holds, from the frame pointer.
        let mut builder = JITBuilder::with_flags(
            &[
                ("preserve_frame_pointers", "true"),
                compile::VERIFIED_ONCE,
                compile::PROBED[0],
                compile::PROBED[1],
            ],
            default_libcall_names(),
        )
        .map_err(|e| e.to_string())?;
        // Code reaches the image's data, such as its slots, by addresses relative to its own,
        // which on aarch64 span 2 GiB: every segment comes from one region reserved at once,
        // and only committed as the image grows, so that none lies out of reach of another.
        // Separate mappings were out of reach under AddressSanitizer, whose own mappings
        // scatter the address space, as `just sanitizers target/differential` found.
        let arena = ArenaMemoryProvider::new_with_size(ARENA)
            .map_err(|e| format!("cannot reserve the image's memory: {e}"))?;
        builder.memory_provider(Box::new(arena));
        let symbols = stilt_runtime::symbols();
        for &(name, address) in &symbols {
            builder.symbol(name, address);
        }
        let available: HashSet<&'static str> = symbols.iter().map(|(n, _)| *n).collect();
        Ok(Self {
            module: Some(JITModule::new(builder)),
            reg: Registry::new(available),
            loaded: HashMap::new(),
            files: Vec::new(),
            registrations: Vec::new(),
        })
    }

    /// Tells the image which functions the check of `without alloc` guards, for the loads that
    /// follow; a function whose guard changes is compiled again ([`crate::guards`]).
    pub fn set_guards(&mut self, guards: stilt_mir::Guards) {
        if *self.reg.guards != guards {
            self.reg.guards = Arc::new(guards);
        }
    }

    /// Tells the image where the program's files are, for the DWARF it gives debuggers.
    pub fn set_files(&mut self, files: Vec<PathBuf>) {
        self.files = files;
    }

    /// An empty image for a watched run, whose code polls the runtime's stop flag on entering
    /// a function and on each loop's back edge, so that the run can be stopped.
    ///
    /// # Errors
    ///
    /// As [`Image::new`].
    pub fn watched() -> Result<Self, String> {
        let mut image = Self::new()?;
        image.reg.watched = true;
        Ok(image)
    }

    /// Compiles the functions whose MIR differs from the image's, and makes each call reach
    /// its new code. Functions the image holds but `functions` doesn't keep their code.
    ///
    /// # Errors
    ///
    /// Fails when a function calls a native the runtime doesn't define, or Cranelift rejects
    /// the code.
    pub fn load(&mut self, functions: &[Arc<Function>]) -> Result<Loaded, String> {
        let module = self.module.as_mut().ok_or("the image is freed")?;
        let guards = Arc::clone(&self.reg.guards);
        let guard_of = |f: &FnRef| guards.get(f).copied();
        let mut changed: Vec<&Arc<Function>> = functions
            .iter()
            .filter(|f| {
                !self.loaded.get(&f.name).is_some_and(|(l, guard)| {
                    (Arc::ptr_eq(l, f) || **l == ***f) && *guard == guard_of(&f.name)
                })
            })
            .collect();
        // A function the load doesn't give whose guard changed is compiled again as it was.
        let given: HashSet<&FnRef> = functions.iter().map(|f| &f.name).collect();
        let regarded: Vec<Arc<Function>> = (self.loaded.iter())
            .filter(|(name, (_, guard))| !given.contains(name) && *guard != guard_of(name))
            .map(|(_, (f, _))| Arc::clone(f))
            .collect();
        changed.extend(&regarded);
        let mut facts = compile::compile(module, &mut self.reg, &changed)?;
        let mut bridges = Vec::new();
        for b in bridges_of(&self.reg, &changed) {
            let id = self.reg.declare_bridge(module, &b)?;
            bridges.push((b, id));
        }
        let declared: Vec<(&Function, FuncId)> = bridges.iter().map(|(b, id)| (b, *id)).collect();
        facts.extend(compile::define(module, &mut self.reg, &declared)?);
        let patching = Instant::now();
        module.finalize_definitions().map_err(|e| e.to_string())?;
        let address = |id| module.get_finalized_function(id) as u64;
        let data = |id| module.get_finalized_data(id).0 as u64;
        let cie = cranelift_module::Module::isa(module).create_systemv_cie();
        if let Some(r) = debug::jit::register(&facts, &self.files, address, data, cie)? {
            self.registrations.push(r);
        }
        for f in &changed {
            let (id, _) = self.reg.code[&f.name];
            self.install(f, id);
            self.forget_constant(&f.name);
        }
        for (b, id) in &bridges {
            self.install(b, *id);
        }
        let compiled = changed.iter().map(|f| f.name.clone()).collect();
        for f in changed {
            let guard = guards.get(&f.name).copied();
            self.loaded.insert(f.name.clone(), (Arc::clone(f), guard));
        }
        Ok(Loaded {
            compiled,
            patching: patching.elapsed(),
        })
    }

    /// Stores the address of the code `id`, compiled from `function`, in the slot of the
    /// convention that code follows.
    fn install(&self, function: &Function, id: FuncId) {
        let Some(module) = self.module.as_ref() else {
            return;
        };
        let code = module.get_finalized_function(id) as u64;
        let owned = module::owned_params(function);
        let Ok(slot) = self.reg.slot_of(&function.name, &owned) else {
            return;
        };
        let (slot, _) = module.get_finalized_data(slot);
        // SAFETY: the slot is a word of writable data that the image allocated, aligned to 8,
        // which running code only loads.
        unsafe { AtomicU64::from_ptr(slot.cast_mut().cast()).store(code, Ordering::Release) };
    }

    /// Forgets the value that a constant whose code changed computed.
    fn forget_constant(&self, f: &FnRef) {
        let Some(module) = self.module.as_ref() else {
            return;
        };
        for (_, constant, _) in self.reg.constants.iter().filter(|(g, ..)| g == f) {
            let (cell, _) = module.get_finalized_data(*constant);
            // SAFETY: a constant's cell is writable words, aligned to 8: whether it is
            // computed, then its value's words.
            unsafe {
                AtomicU64::from_ptr(cell.cast_mut().cast()).store(0, Ordering::Release);
            }
        }
    }

    /// Releases the value of every constant that the program computed, and forgets it, as the
    /// program's entry does when it ends: for the tests of `stilt test`, whose entries keep the
    /// constants for the tests after them, once no code of the image runs.
    pub fn release_constants(&self) {
        let Some(module) = self.module.as_ref() else {
            return;
        };
        for (_, constant, words) in &self.reg.constants {
            let (cell, _) = module.get_finalized_data(*constant);
            let cell: *mut u64 = cell.cast_mut().cast();
            // SAFETY: a constant's cell is writable words, aligned to 8: its state, 1 once it is
            // computed, then its value's words, of which each heap word owns a reference; no
            // code of the image runs to read them.
            unsafe {
                if *cell != 1 {
                    continue;
                }
                for i in heap_words(words) {
                    stilt_runtime::release(*cell.add(1 + i));
                }
                *cell = 0;
            }
        }
    }

    /// The program's entry, as the runtime runs it: the latest code of `#main`.
    ///
    /// # Errors
    ///
    /// Fails when the image has no entry.
    pub fn entry(&self) -> Result<stilt_runtime::Entry, String> {
        self.entry_of(&FnRef::Main)
    }

    /// The latest code of an entry: the program's, a test's (`FnRef::TestEntry`), a
    /// property's (`FnRef::PropEntry`), or an input's of the REPL (`FnRef::InputEntry`).
    ///
    /// # Errors
    ///
    /// Fails when the image doesn't hold `f`, or `f` isn't an entry.
    pub fn entry_of(&self, f: &FnRef) -> Result<stilt_runtime::Entry, String> {
        if !matches!(
            f,
            FnRef::Main | FnRef::TestEntry(..) | FnRef::PropEntry(..) | FnRef::InputEntry(_)
        ) {
            return Err(format!("{f} is no entry"));
        }
        let module = self.module.as_ref().ok_or("the image is freed")?;
        let &(id, _) = self
            .reg
            .code
            .get(f)
            .ok_or_else(|| format!("the image doesn't hold {f}"))?;
        let code = module.get_finalized_function(id);
        // SAFETY: an entry is compiled with the signature `Entry`: one word in, the result and
        // the raised flag out.
        Ok(unsafe { std::mem::transmute::<*const u8, stilt_runtime::Entry>(code) })
    }
}

impl Drop for Image {
    fn drop(&mut self) {
        // Debuggers forget the code before its memory goes.
        self.registrations.clear();
        // A program that ended with a panic, or that never ended, as `stilt run` stops one, leaves
        // the values of the constants it computed, which the image owns: they go with it.
        self.release_constants();
        if let Some(module) = self.module.take() {
            // SAFETY: the image is dropped only once no program runs its code.
            unsafe { module.free_memory() };
        }
    }
}

/// The bridges that keep the slot of each earlier convention of a changed function reaching
/// its new code (`crate::bridge`).
fn bridges_of(reg: &Registry, changed: &[&Arc<Function>]) -> Vec<Function> {
    changed
        .iter()
        .flat_map(|f| {
            let current = module::owned_params(f);
            reg.conventions(&f.name)
                .into_iter()
                .filter(move |c| *c != current)
                .map(move |c| bridge::bridge(f, &c))
        })
        .collect()
}

/// Compiles the functions of a program, its entry among them, into a new image.
///
/// # Errors
///
/// As [`Image::load`].
pub fn jit(functions: &[Arc<Function>], files: Vec<PathBuf>) -> Result<Image, String> {
    let mut image = Image::new()?;
    image.set_files(files);
    image.load(functions)?;
    Ok(image)
}

/// The index of each heap word among the words of a value of the representations `reprs`, one
/// after the other, those of arrays held in memory among them. A constant's type names no type
/// parameter (declarations.constant-declarations), so each word is a heap word or not.
fn heap_words(reprs: &[stilt_mir::mir::Repr]) -> Vec<usize> {
    use stilt_mir::mir::Repr;
    let mut out = Vec::new();
    let mut at = 0;
    for &r in reprs {
        match r {
            Repr::Heap => out.push(at),
            Repr::Array(e) => {
                let each = heap_words(e.each());
                let width = e.element_words();
                for k in 0..e.len() as usize {
                    out.extend(each.iter().map(|j| at + k * width + j));
                }
            }
            Repr::Scalar | Repr::Generic(_) => {}
        }
        at += r.words();
    }
    out
}
