//! What the modes read of the functions a body calls by name: the function a call names, and the
//! parameters it consumes (values.consumed-parameters), by their places among the source's
//! parameters, a method's receiver first, as a typed call's arguments are.

use stilt_hir::hir::Name;

use stilt_db::{Db, Program};
use stilt_mir::{Code, FnRef, bodies, code_of};
use stilt_types::tast::Callee;
use stilt_types::ty::Ty;

use crate::queries::{consumed, source_name};

/// The function that a call by name calls, if it is one with a body or a native: a function of
/// a module, of an inherent impl, or of a trait impl for a named type, its own or the trait's
/// default. A method called on a type parameter goes through a dictionary, and a structural
/// impl's through code the compiler writes, so neither names one.
pub(crate) fn callee(db: &dyn Db, program: Program, c: &Callee) -> Option<FnRef> {
    match c {
        Callee::Function(item) => Some(FnRef::Function(item.clone())),
        Callee::Member(owner, name) => Some(FnRef::Member(owner.clone(), *name)),
        Callee::TraitMethod(t, name, Ty::Con(owner, _)) => {
            let code = &bodies(db, program).code;
            let own = FnRef::ImplMethod(t.clone(), owner.clone(), *name);
            if code.contains_key(&own) {
                return Some(own);
            }
            let default = FnRef::DefaultMethod(t.clone(), *name);
            code.contains_key(&default).then_some(default)
        }
        Callee::TraitMethod(..) | Callee::Operation(..) => None,
    }
}

/// The parameters of `f`, by their places among the source's, that it consumes. Consumption is
/// inferred on its code, whose parameters are the words of the source's, named after them, and
/// the hidden ones of its generics, which have no name.
pub(crate) fn consumed_params(db: &dyn Db, program: Program, f: &FnRef) -> Vec<usize> {
    let owned = consumed(db, program, f.clone());
    if owned.is_empty() {
        return Vec::new();
    }
    let Some(Code::Body(file, index)) = code_of(db, program, f.clone()) else {
        return Vec::new();
    };
    let functions = stilt_mir::functions(db, program, f.clone());
    let Some(code) = functions.iter().find(|g| g.name == *f) else {
        return Vec::new();
    };
    let names: Vec<Name> = owned.iter().filter_map(|&i| source_name(code, i)).collect();
    let body = stilt_hir::module_body(db, program, file, index);
    body.params
        .iter()
        .enumerate()
        .filter(|(_, v)| names.contains(&body.locals[v.0 as usize].name))
        .map(|(i, _)| i)
        .collect()
}
