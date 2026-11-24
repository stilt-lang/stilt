//! Compiling MIR functions into a module, the JIT's or an object file's.
//!
//! Each function is translated into Cranelift's IR one at a time, since translating declares
//! what it names in the module; the IR is then compiled into machine code across the machine's
//! cores, or `STILT_THREADS` of them, which needs only the target; and the code is defined in
//! the module in the order of the functions, so that the module, and the object file or image
//! it makes, is the same byte for byte whatever the number of threads (goal clean-debug-build).
//! Cranelift's verifier checks the IR of each function once, before it is compiled, rather
//! than again after each of Cranelift's own passes, which cost a `stilt run` of a small
//! program a seventh of its time.

use std::sync::Arc;

use cranelift_codegen::control::ControlPlane;
use cranelift_codegen::ir::{Function as ClifFunction, StackSlot};
use cranelift_codegen::isa::TargetIsa;
use cranelift_codegen::{CodegenError, Context};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Module, ModuleError, ModuleReloc};
use stilt_db::parallel;
use stilt_mir::FnRef;
use stilt_mir::mir::{Function, Local};

use crate::debug::piece::Piece;
use crate::debug::{self, Constant, Facts};
use crate::module::{Registry, signature};
use crate::translate::Translator;

/// The setting that leaves Cranelift's verifier off in an ISA, since [`Translated::compile`]
/// runs it once on the IR of each function, before compiling it.
pub(crate) const VERIFIED_ONCE: (&str, &str) = ("enable_verifier", "false");

/// The settings that make a function whose frame is larger than a page touch each page of it, from
/// the top, as it starts: a frame that holds a large array (generics.large-arrays) past the end of
/// the stack then faults on the stack's guard, which the runtime reports as a stack overflow
/// (program.exit-statuses), instead of reaching past the guard into other memory.
pub(crate) const PROBED: [(&str, &str); 2] = [
    ("enable_probestack", "true"),
    ("probestack_strategy", "inline"),
];

/// Declares a new version of each function, then compiles them all into `module`, and with
/// `reg.debug`, returns what debuggers need of each (goal debuggable-builds).
pub(crate) fn compile(
    module: &mut dyn Module,
    reg: &mut Registry,
    functions: &[&Arc<Function>],
) -> Result<Vec<Arc<Piece>>, String> {
    let mut declared = Vec::with_capacity(functions.len());
    for f in functions {
        declared.push((&***f, reg.declare(module, f)?));
    }
    define(module, reg, &declared)
}

/// Compiles functions that are declared, each into the function of `module` it is given with,
/// and with `reg.debug`, returns what debuggers need of each.
pub(crate) fn define(
    module: &mut dyn Module,
    reg: &mut Registry,
    functions: &[(&Function, FuncId)],
) -> Result<Vec<Arc<Piece>>, String> {
    // The entry releases the constants, which the other functions register as they read them,
    // so it is translated last.
    let (main, others): (Vec<_>, Vec<_>) =
        functions.iter().partition(|(f, _)| f.name == FnRef::Main);
    let mut fbc = FunctionBuilderContext::new();
    let mut translated = Vec::with_capacity(functions.len());
    for &(f, id) in others.into_iter().chain(main) {
        translated.push(translate(module, reg, &mut fbc, f, id)?);
    }
    let compiled = compile_all(translated, module.isa(), reg.debug);
    let mut facts = Vec::new();
    for c in compiled {
        let c = c?;
        module
            .define_function_bytes(c.id, c.alignment, &c.bytes, &c.relocs)
            .map_err(|e| format!("cannot compile {}: {e:?}", c.name))?;
        facts.extend(c.dwarf);
    }
    Ok(facts)
}

/// Compiles the translated functions across the machine's cores, the largest first, so that
/// the last to finish is a small one, and gives their code in their order.
pub(crate) fn compile_all(
    translated: Vec<Translated<'_>>,
    isa: &dyn TargetIsa,
    debug: bool,
) -> Vec<Result<Compiled, String>> {
    let mut largest_first: Vec<(usize, Translated<'_>)> =
        translated.into_iter().enumerate().collect();
    largest_first.sort_by_key(|(_, t)| std::cmp::Reverse(t.ir.dfg.num_insts()));
    let mut compiled = parallel::map_costly(largest_first, |(i, t)| (i, t.compile(isa, debug)));
    compiled.sort_unstable_by_key(|&(i, _)| i);
    compiled.into_iter().map(|(_, c)| c).collect()
}

/// A function translated into Cranelift's IR, with what its debug facts need.
pub(crate) struct Translated<'f> {
    function: &'f Function,
    id: FuncId,
    ir: ClifFunction,
    /// The location word of each source location the IR marks.
    locs: Vec<u64>,
    /// The slot of each named array held in memory, and its offset there.
    arrays: Vec<(Local, StackSlot, i32)>,
    constants: Vec<Option<Constant>>,
}

/// A function's machine code, ready to be defined in its module, with its DWARF.
pub(crate) struct Compiled {
    pub(crate) name: FnRef,
    pub(crate) id: FuncId,
    pub(crate) alignment: u64,
    pub(crate) bytes: Vec<u8>,
    pub(crate) relocs: Vec<ModuleReloc>,
    pub(crate) dwarf: Option<Arc<Piece>>,
}

/// Translates `f` into Cranelift's IR, declaring in `module` what it names.
pub(crate) fn translate<'f>(
    module: &mut dyn Module,
    reg: &mut Registry,
    fbc: &mut FunctionBuilderContext,
    f: &'f Function,
    id: FuncId,
) -> Result<Translated<'f>, String> {
    let mut ir = ClifFunction::new();
    ir.signature = signature(module, f.params.len(), f.results as usize);
    if reg.debug {
        ir.collect_debug_info();
    }
    let config = module.isa().frontend_config();
    let mut t = Translator::new(FunctionBuilder::new(&mut ir, fbc), module, reg, f);
    t.run()?;
    let labels = t.finish(config);
    let constants = if reg.debug {
        debug::label(&mut ir, &labels.values);
        debug::constants(f, |c| reg.data(module, c))?
    } else {
        Vec::new()
    };
    Ok(Translated {
        function: f,
        id,
        ir,
        locs: labels.locs,
        arrays: labels.arrays,
        constants,
    })
}

impl Translated<'_> {
    /// Compiles the function for `isa`, as its module would, and with `debug`, writes its
    /// DWARF.
    pub(crate) fn compile(self, isa: &dyn TargetIsa, debug: bool) -> Result<Compiled, String> {
        let (mut compiled, facts) = self.compiled(isa, debug)?;
        compiled.dwarf = facts.map(|f| {
            let fp = debug::frame_pointer(isa);
            Arc::new(Piece::new(&f, fp, isa.create_systemv_cie().as_ref()))
        });
        Ok(compiled)
    }

    /// What debuggers need of the function compiled for `isa`.
    #[cfg(test)]
    pub(crate) fn facts(self, isa: &dyn TargetIsa) -> Result<Facts, String> {
        let (_, facts) = self.compiled(isa, true)?;
        facts.ok_or_else(|| "no facts".to_owned())
    }

    /// The function compiled for `isa`, and with `debug`, what debuggers need of it.
    /// Cranelift's verifier checks the IR that translation made, once: the ISA leaves it off
    /// ([`VERIFIED_ONCE`]), since Cranelift would run it again on the same IR and after each
    /// of its own passes.
    fn compiled(
        self,
        isa: &dyn TargetIsa,
        debug: bool,
    ) -> Result<(Compiled, Option<Facts>), String> {
        let name = &self.function.name;
        let mut ctx = Context::for_function(self.ir);
        let failed = |e| format!("cannot compile {name}: {:?}", ModuleError::Compilation(e));
        ctx.verify(isa)
            .map_err(|errors| failed(CodegenError::Verifier(errors)))?;
        let alignment = ctx
            .compile(isa, &mut ControlPlane::default())
            .map(|code| u64::from(code.buffer.min_alignment))
            .map_err(|e| failed(e.inner))?;
        let code = ctx.compiled_code().ok_or("Cranelift compiled no code")?;
        let relocs = code
            .buffer
            .relocs()
            .iter()
            .map(|r| ModuleReloc::from_mach_reloc(r, &ctx.func, self.id))
            .collect();
        let facts = debug.then(|| {
            let base = ctx.func.params.base_srcloc();
            let f = self.function;
            let marks = debug::Marks {
                locs: &self.locs,
                base,
                constants: &self.constants,
                arrays: &self.arrays,
            };
            debug::facts(isa, self.id, f, code, &marks)
        });
        let compiled = Compiled {
            name: name.clone(),
            id: self.id,
            alignment,
            bytes: code.code_buffer().to_vec(),
            relocs,
            dwarf: None,
        };
        Ok((compiled, facts))
    }
}
