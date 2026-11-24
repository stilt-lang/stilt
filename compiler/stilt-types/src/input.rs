//! An input of the REPL, checked in its module's scope (repl.input-checking): type checking, as a
//! test's body of the module is checked, then the later phases, as for a body of the program
//! (errors.phases).

use stilt_db::{Db, Program, SourceFile};
use stilt_diag::Diagnostic;
use stilt_hir::decls::QueriedOnce;
use stilt_hir::hir::{self, GenericId};

use crate::analyses::{self, SigInfo};
use crate::infer::Env;
use crate::queries::{generic_name, module_info, visible_traits};
use crate::tast::{Code, Definition, TypedBody};
use crate::ty::Ty;

/// An input, checked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Checked {
    /// Its typed body.
    pub body: TypedBody,
    /// The type of its value.
    pub ty: Ty,
    /// Its diagnostics of every phase, at the input's own positions.
    pub diagnostics: Vec<Diagnostic>,
}

/// Checks an input's body, resolved in the module of `file`, whose parameters have the types
/// `params`.
#[must_use]
pub fn check_input(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    body: &hir::Body,
    params: &[Ty],
) -> Checked {
    let module = module_info(db, program, file);
    let decls = QueriedOnce::new(db, program);
    let names = |id: &GenericId| *generic_name(db, program, id.clone());
    let env = Env {
        decls: &decls,
        module: module.name,
        std: module.std,
        traits: visible_traits(&decls, module),
        bounds: Vec::new(),
        bound_args: Vec::new(),
        self_ty: None,
        names: &names,
        imports: &module.imports,
        signature: None,
        main: false,
        procedural: false,
        renames: &stilt_pkg::edition::renames(module.edition),
    };
    let (typed, ty, mut diagnostics) = crate::infer::check_input(env, body, params);
    if let Definition::Code(Code::Block(block)) = &typed.code {
        let sig = SigInfo {
            names: &names,
            params: body
                .params
                .iter()
                .map(|v| {
                    let local = &body.locals[v.0 as usize];
                    (local.name, local.at)
                })
                .collect(),
            spans: None,
            module: &module.name,
            imports: &module.imports,
            raise_broken: false,
            text: &|| None,
            line: &|_| 0,
            block_end: None,
            projection: false,
            analysed: &[],
        };
        diagnostics.extend(analyses::check(
            &decls,
            &sig,
            &typed,
            block,
            None,
            None,
            Vec::new(),
        ));
    }
    Checked {
        body: typed,
        ty,
        diagnostics,
    }
}

/// A type as a program writes it, for the answers of the REPL (repl.answers).
#[must_use]
pub fn shown(db: &dyn Db, program: Program, ty: &Ty) -> String {
    let names = |id: &GenericId| *generic_name(db, program, id.clone());
    crate::ty::Table::default().show(ty, &names)
}
