//! A program compiled into an object file for a target, which `stilt build` links with the
//! target's runtime library into an executable (goal cross-compilation).
//!
//! The object holds every function the program's entry reaches, each reached through its slot
//! as in memory, and a C `main` that hands the entry, the paths of the program's files and the
//! arguments to the runtime's `stilt_rt_start`, which runs the program and returns its exit
//! status. A build compiles only the functions whose code changed since the build whose code
//! it is given ([`Built`]), and defines the others from that code.

use std::collections::HashSet;
use std::path::PathBuf;
use std::sync::Arc;

use cranelift_codegen::ir::{AbiParam, InstBuilder, types::I32, types::I64};
use cranelift_codegen::isa::{self, OwnedTargetIsa};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, Linkage, Module, default_libcall_names};
use cranelift_object::{ObjectBuilder, ObjectModule};
use stilt_mir::FnRef;
use stilt_mir::mir::Function;

use crate::module::{Registry, runtime_signature};
use crate::reuse::Built;
use crate::target::Target;

/// The object file of a program for `target`: its functions, the entry among them, and a C `main`,
/// with their DWARF (goal debuggable-builds). `files` are the paths of the program's files as its
/// panics report them, and `paths` where they are, which debuggers read. The code of each function
/// that `built` holds from the same MIR is reused, and `built` then holds the code of this build's
/// functions; the object is the same byte for byte whatever it held.
///
/// # Errors
///
/// Fails when a function calls a native the runtime doesn't define, or Cranelift rejects the
/// code.
pub fn object(
    (functions, guards): (&[Arc<Function>], stilt_mir::Guards),
    files: &[String],
    paths: &[PathBuf],
    (target, built): (Target, &mut Built),
) -> Result<Vec<u8>, String> {
    let isa = isa(target)?;
    let (mut module, mut reg) = module_for(OwnedTargetIsa::clone(&isa))?;
    reg.guards = Arc::new(guards);
    let facts = crate::reuse::compile(&mut module, &mut reg, functions, (built, target, &*isa))?;
    c_main(&mut module, &mut reg, files)?;
    let cie = module.isa().create_systemv_cie();
    let mut product = module.finish();
    let placing = crate::debug::sections::add_to_object(&mut product, &facts, paths, cie)?;
    let mut bytes = product.emit().map_err(|e| e.to_string())?;
    placing.place(&mut bytes)?;
    stilt_db::parallel::free((reg, facts));
    Ok(bytes)
}

/// An empty object module for `target`, and the registry of what it declares.
#[cfg(test)]
pub(crate) fn module(target: Target) -> Result<(ObjectModule, Registry), String> {
    module_for(isa(target)?)
}

/// The ISA of `target`, with the settings of a build.
pub(crate) fn isa(target: Target) -> Result<OwnedTargetIsa, String> {
    let mut flags = settings::builder();
    flags.set("is_pic", "true").map_err(|e| e.to_string())?;
    // Debuggers find each frame, and the locals it holds, from the frame pointer.
    flags
        .set("preserve_frame_pointers", "true")
        .map_err(|e| e.to_string())?;
    flags.set("opt_level", "speed").map_err(|e| e.to_string())?;
    let (verifier, off) = crate::compile::VERIFIED_ONCE;
    flags.set(verifier, off).map_err(|e| e.to_string())?;
    for (name, value) in crate::compile::PROBED {
        flags.set(name, value).map_err(|e| e.to_string())?;
    }
    let triple = target
        .triple()
        .parse()
        .map_err(|e| format!("{}: {e}", target.triple()))?;
    isa::lookup(triple)
        .map_err(|e| format!("{target}: {e}"))?
        .finish(settings::Flags::new(flags))
        .map_err(|e| e.to_string())
}

/// An empty object module for `isa`, and the registry of what it declares.
pub(crate) fn module_for(isa: OwnedTargetIsa) -> Result<(ObjectModule, Registry), String> {
    let builder =
        ObjectBuilder::new(isa, "stilt", default_libcall_names()).map_err(|e| e.to_string())?;
    let available: HashSet<&'static str> =
        stilt_runtime::symbols().iter().map(|(n, _)| *n).collect();
    let mut reg = Registry::new(available);
    reg.object = true;
    Ok((ObjectModule::new(builder), reg))
}

/// The table of the program's files, each ended by a NUL and the whole by an empty one, as the
/// runtime reads it.
pub(crate) fn files_table(
    module: &mut ObjectModule,
    reg: &mut Registry,
    files: &[String],
) -> Result<cranelift_module::DataId, String> {
    let table = reg.fresh_data(module, false)?;
    let mut bytes = Vec::new();
    for path in files {
        bytes.extend_from_slice(path.as_bytes());
        bytes.push(0);
    }
    bytes.push(0);
    let mut desc = DataDescription::new();
    desc.define(bytes.into_boxed_slice());
    module
        .define_data(table, &desc)
        .map_err(|e| e.to_string())?;
    Ok(table)
}

/// Defines C's `main`, which returns `stilt_rt_start` of its arguments, the entry, the table of
/// the program's files and 1, since a debug build checks its counts at its end
/// (cycles.check-at-exit).
fn c_main(module: &mut ObjectModule, reg: &mut Registry, files: &[String]) -> Result<(), String> {
    let table = files_table(module, reg, files)?;
    let mut sig = module.make_signature();
    sig.params.extend([AbiParam::new(I32), AbiParam::new(I64)]);
    sig.returns.push(AbiParam::new(I32));
    let main = module
        .declare_function("main", Linkage::Export, &sig)
        .map_err(|e| e.to_string())?;
    let start_sig = runtime_signature(module, 5, true);
    let start = reg.import(module, "stilt_rt_start", &start_sig)?;
    let &(entry, _) = reg
        .code
        .get(&FnRef::Main)
        .ok_or("the program has no entry")?;

    let mut ctx = module.make_context();
    ctx.func.signature = sig;
    let mut fbc = FunctionBuilderContext::new();
    let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fbc);
    let block = fb.create_block();
    fb.append_block_params_for_function_params(block);
    fb.switch_to_block(block);
    let (count, vector) = (fb.block_params(block)[0], fb.block_params(block)[1]);
    let count = fb.ins().sextend(I64, count);
    let entry = module.declare_func_in_func(entry, fb.func);
    let entry = fb.ins().func_addr(I64, entry);
    let table = module.declare_data_in_func(table, fb.func);
    let table = fb.ins().symbol_value(I64, table);
    let start = module.declare_func_in_func(start, fb.func);
    let counts = fb.ins().iconst(I64, 1);
    let call = fb.ins().call(start, &[count, vector, entry, table, counts]);
    let status = fb.inst_results(call)[0];
    let status = fb.ins().ireduce(I32, status);
    fb.ins().return_(&[status]);
    fb.seal_all_blocks();
    fb.finalize(module.isa().frontend_config());
    ctx.verify(module.isa())
        .map_err(|e| format!("cannot compile main: {e:?}"))?;
    module
        .define_function(main, &mut ctx)
        .map_err(|e| format!("cannot compile main: {e:?}"))
}
