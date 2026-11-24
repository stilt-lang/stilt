//! Translating functions apart, across the machine's cores (goals clean-debug-build and
//! compile-time-code-rebuilds).
//!
//! Translation declares in its module what a function names as it first meets it, so
//! translating into the module takes the functions one at a time, in their order. A build
//! translates each function whose code it doesn't keep into a draft of its own instead: a module
//! that only numbers what it declares, and a registry that knows the functions the module
//! compiles ([`Registry::draft`]), so that the translation asks what translating into the module
//! asks, in the same order, and gets numbers of its own. The same thread then compiles it, while
//! the build asks what it asked again of the module's registry, in the order of the functions,
//! as it asks again what the code it keeps asked ([`crate::reuse`]): everything is declared in
//! the order and under the names that translating into the module gives it, and the draft's
//! code is relocated against the answers.

use std::sync::Arc;

use cranelift_codegen::Context;
use cranelift_codegen::control::ControlPlane;
use cranelift_codegen::ir::Signature;
use cranelift_codegen::isa::TargetIsa;
use cranelift_frontend::FunctionBuilderContext;
use cranelift_module::{
    DataDescription, DataId, FuncId, Linkage, Module, ModuleDeclarations, ModuleReloc, ModuleResult,
};
use stilt_mir::mir::Function;

use crate::compile::{Compiled, translate};
use crate::module::{Answer, Asked, Registry, signature};

/// A module that numbers what translation declares in it, and keeps no code or data.
struct Draft<'a> {
    isa: &'a dyn TargetIsa,
    declarations: ModuleDeclarations,
}

impl Module for Draft<'_> {
    fn isa(&self) -> &dyn TargetIsa {
        self.isa
    }

    fn declarations(&self) -> &ModuleDeclarations {
        &self.declarations
    }

    fn declare_function(
        &mut self,
        name: &str,
        linkage: Linkage,
        signature: &Signature,
    ) -> ModuleResult<FuncId> {
        let (id, _) = (self.declarations).declare_function(name, linkage, signature)?;
        Ok(id)
    }

    fn declare_anonymous_function(&mut self, signature: &Signature) -> ModuleResult<FuncId> {
        self.declarations.declare_anonymous_function(signature)
    }

    fn declare_data(
        &mut self,
        name: &str,
        linkage: Linkage,
        writable: bool,
        tls: bool,
    ) -> ModuleResult<DataId> {
        let (id, _) = (self.declarations).declare_data(name, linkage, writable, tls)?;
        Ok(id)
    }

    fn declare_anonymous_data(&mut self, writable: bool, tls: bool) -> ModuleResult<DataId> {
        self.declarations.declare_anonymous_data(writable, tls)
    }

    fn define_function_with_control_plane(
        &mut self,
        _: FuncId,
        _: &mut Context,
        _: &mut ControlPlane,
    ) -> ModuleResult<()> {
        Ok(())
    }

    fn define_function_bytes(
        &mut self,
        _: FuncId,
        _: u64,
        _: &[u8],
        _: &[ModuleReloc],
    ) -> ModuleResult<()> {
        Ok(())
    }

    fn define_data(&mut self, _: DataId, _: &DataDescription) -> ModuleResult<()> {
        Ok(())
    }
}

/// What a draft's translation asked, each once, with the answers the draft gave.
pub(crate) type Asks = Vec<(Asked, Answer)>;

/// A function to translate apart and compile: its MIR, and the registry it is translated with.
pub(crate) struct Drafting<'f> {
    function: &'f Arc<Function>,
    reg: Registry,
}

/// The drafts of `drafted`, among the `functions` that `reg`'s module compiles, the largest
/// first, so that the last to be compiled is a small one, each with its place among `drafted`.
pub(crate) fn drafts<'f>(
    reg: &Registry,
    functions: &[Arc<Function>],
    drafted: Vec<&'f Arc<Function>>,
) -> Vec<(usize, Drafting<'f>)> {
    let known = crate::module::known(functions);
    let mut drafts: Vec<(usize, Drafting<'f>)> = (drafted.into_iter().enumerate())
        .map(|(at, function)| {
            let reg = reg.draft(&known);
            (at, Drafting { function, reg })
        })
        .collect();
    drafts.sort_by_key(|(_, d)| {
        let blocks = d.function.blocks.iter();
        std::cmp::Reverse(blocks.map(|b| b.stmts.len() + 1).sum::<usize>())
    });
    drafts
}

impl Drafting<'_> {
    /// Translates the function into a draft of its own and compiles it for `isa`, with its
    /// DWARF when `debug`, giving what the translation asked by `asked` as soon as it is
    /// translated, so that the build asks it again while the function is compiled. The draft
    /// numbers the function's code itself, as the module may not have yet, so the build gives
    /// the code the module's number once it is compiled ([`crate::reuse`]).
    pub(crate) fn compile(
        mut self,
        isa: &dyn TargetIsa,
        debug: bool,
        asked: &dyn Fn(Result<Asks, String>),
    ) -> Result<Compiled, String> {
        let mut module = Draft {
            isa,
            declarations: ModuleDeclarations::default(),
        };
        let f = self.function;
        let sig = signature(&module, f.params.len(), f.results as usize);
        self.reg.asked = Some(Vec::new());
        let mut fbc = FunctionBuilderContext::new();
        let translated = (module.declarations.declare_anonymous_function(&sig))
            .map_err(|e| format!("cannot declare {}: {e}", f.name))
            .and_then(|id| translate(&mut module, &mut self.reg, &mut fbc, f, id));
        match translated {
            Ok(translated) => {
                let asks = self.reg.asked.take().unwrap_or_default();
                asked(Ok(crate::reuse::once_each(asks)));
                translated.compile(isa, debug)
            }
            Err(e) => {
                asked(Err(e.clone()));
                Err(e)
            }
        }
    }
}
