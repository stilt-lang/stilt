//! A library's object file, which `stilt build --lib` archives with the target's runtime
//! library (c.calls-from-c and c.static-library).
//!
//! The object holds every function the exported functions reach, and for each of these a C
//! function under its own name, which takes and returns its values as C passes them: it makes the
//! runtime ready, through `stilt_runtime_once`, calls the compiled function with each value in
//! a word, as compiled code holds it, makes what the call wrote reach its file, and returns the
//! result as C takes it. `stilt_runtime_once` is defined here, so that a C program that links
//! two Stilt libraries is rejected by its linker.

use std::path::PathBuf;
use std::sync::Arc;

use cranelift_codegen::ir::{AbiParam, InstBuilder, MemFlagsData, Type, Value, types};
use cranelift_codegen::isa::OwnedTargetIsa;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::ObjectModule;
use stilt_mir::mir::Function;
use stilt_mir::{CType, Export, FnRef};

use crate::module::{Registry, runtime_signature};
use crate::object::{files_table, isa, module_for};
use crate::reuse::Built;
use crate::target::Target;

/// The object file of a library for `target`: the functions that `exports` reach, a C function
/// for each export, and `stilt_runtime_once`, with their DWARF. `files` and `paths` are as for
/// [`crate::object`].
///
/// # Errors
///
/// Fails when a function calls a native the runtime doesn't define, an export's function wasn't
/// compiled, or Cranelift rejects the code.
pub fn library(
    functions: &[Arc<Function>],
    files: &[String],
    paths: &[PathBuf],
    (target, exports): (Target, &[Export]),
) -> Result<Vec<u8>, String> {
    let isa = isa(target)?;
    let (mut module, mut reg) = module_for(OwnedTargetIsa::clone(&isa))?;
    let mut built = Built::default();
    let facts = crate::reuse::compile(
        &mut module,
        &mut reg,
        functions,
        (&mut built, target, &*isa),
    )?;
    let once = runtime_once(&mut module, &mut reg, files)?;
    for export in exports {
        wrapper(&mut module, &mut reg, export, once)
            .map_err(|e| format!("cannot compile {}: {e}", export.symbol))?;
    }
    let cie = module.isa().create_systemv_cie();
    let mut product = module.finish();
    let placing = crate::debug::sections::add_to_object(&mut product, &facts, paths, cie)?;
    let mut bytes = product.emit().map_err(|e| e.to_string())?;
    placing.place(&mut bytes)?;
    stilt_db::parallel::free((reg, facts, built));
    Ok(bytes)
}

/// Defines `stilt_runtime_once`, which makes the runtime ready with the table of the program's
/// files.
fn runtime_once(
    module: &mut ObjectModule,
    reg: &mut Registry,
    files: &[String],
) -> Result<FuncId, String> {
    let table = files_table(module, reg, files)?;
    let sig = module.make_signature();
    let once = module
        .declare_function("stilt_runtime_once", Linkage::Export, &sig)
        .map_err(|e| e.to_string())?;
    let ready_sig = runtime_signature(module, 1, false);
    let ready = reg.import(module, "stilt_rt_ready", &ready_sig)?;
    let mut ctx = module.make_context();
    ctx.func.signature = sig;
    let mut fbc = FunctionBuilderContext::new();
    let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fbc);
    let block = fb.create_block();
    fb.switch_to_block(block);
    let table = module.declare_data_in_func(table, fb.func);
    let table = fb.ins().symbol_value(types::I64, table);
    let ready = module.declare_func_in_func(ready, fb.func);
    fb.ins().call(ready, &[table]);
    fb.ins().return_(&[]);
    fb.seal_all_blocks();
    fb.finalize(module.isa().frontend_config());
    module
        .define_function(once, &mut ctx)
        .map_err(|e| format!("cannot compile stilt_runtime_once: {e:?}"))?;
    Ok(once)
}

/// The Cranelift type that C passes a value of type `t` in, extended as C extends it.
pub(crate) fn c_param(t: CType) -> AbiParam {
    let param = AbiParam::new(c_type(t));
    match t {
        CType::I8 | CType::I16 | CType::I32 => param.sext(),
        CType::U8 | CType::U16 | CType::U32 | CType::Bool => param.uext(),
        _ => param,
    }
}

fn c_type(t: CType) -> Type {
    match (t.float(), t.bits()) {
        (true, 32) => types::F32,
        (true, _) => types::F64,
        (false, 8) => types::I8,
        (false, 16) => types::I16,
        (false, 32) => types::I32,
        (false, _) => types::I64,
    }
}

/// Defines the C function of `export`, which calls its compiled function between the runtime's
/// readying and the end of the call.
fn wrapper(
    module: &mut ObjectModule,
    reg: &mut Registry,
    export: &Export,
    once: FuncId,
) -> Result<(), String> {
    let code = FnRef::Function(export.item.clone());
    let &(compiled, _) = reg.code.get(&code).ok_or("its function wasn't compiled")?;
    let mut sig = module.make_signature();
    sig.params.extend(export.params.iter().map(|&t| c_param(t)));
    sig.returns.extend(export.result.map(c_param));
    let id = module
        .declare_function(&export.symbol, Linkage::Export, &sig)
        .map_err(|e| e.to_string())?;
    let returned_sig = runtime_signature(module, 0, false);
    let returned = reg.import(module, "stilt_rt_returned", &returned_sig)?;
    let mut ctx = module.make_context();
    ctx.func.signature = sig;
    let mut fbc = FunctionBuilderContext::new();
    let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fbc);
    let block = fb.create_block();
    fb.append_block_params_for_function_params(block);
    fb.switch_to_block(block);
    let once = module.declare_func_in_func(once, fb.func);
    fb.ins().call(once, &[]);
    // The location word of a call from outside the program, as the entry's is.
    let mut args = vec![fb.ins().iconst(types::I64, 0)];
    let params = fb.block_params(block).to_vec();
    for (&value, &t) in params.iter().zip(&export.params) {
        args.push(to_word(&mut fb, value, t));
    }
    let compiled = module.declare_func_in_func(compiled, fb.func);
    let call = fb.ins().call(compiled, &args);
    let results = fb.inst_results(call).to_vec();
    let returned = module.declare_func_in_func(returned, fb.func);
    fb.ins().call(returned, &[]);
    match export.result {
        Some(t) => {
            let value = from_word(&mut fb, results[0], t);
            fb.ins().return_(&[value]);
        }
        None => {
            fb.ins().return_(&[]);
        }
    }
    fb.seal_all_blocks();
    fb.finalize(module.isa().frontend_config());
    module
        .define_function(id, &mut ctx)
        .map_err(|e| format!("{e:?}"))
}

/// The word that compiled code holds a value of type `t` in, which C passed as `value`: an
/// integer extended by its sign or with zeros, a `bool` as 0 or 1, an `f64`'s bits, and an
/// `f32`'s bits in the low half.
pub(crate) fn to_word(fb: &mut FunctionBuilder<'_>, value: Value, t: CType) -> Value {
    let plain = MemFlagsData::new();
    match (t.float(), t.bits()) {
        (true, 32) => {
            let bits = fb.ins().bitcast(types::I32, plain, value);
            fb.ins().uextend(types::I64, bits)
        }
        (true, _) => fb.ins().bitcast(types::I64, plain, value),
        (false, 64) => value,
        (false, _) if t.signed() => fb.ins().sextend(types::I64, value),
        (false, _) => fb.ins().uextend(types::I64, value),
    }
}

/// The value of type `t` that C takes, of the word compiled code holds it in.
pub(crate) fn from_word(fb: &mut FunctionBuilder<'_>, word: Value, t: CType) -> Value {
    let plain = MemFlagsData::new();
    match (t.float(), t.bits()) {
        (true, 32) => {
            let bits = fb.ins().ireduce(types::I32, word);
            fb.ins().bitcast(types::F32, plain, bits)
        }
        (true, _) => fb.ins().bitcast(types::F64, plain, word),
        (false, 64) => word,
        (false, _) => fb.ins().ireduce(c_type(t), word),
    }
}
