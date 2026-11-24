//! Whether a module uses the features of polymorphism.advanced-tier that put it in the advanced
//! tier (polymorphism.advanced-tier and polymorphism.lazy-values; program.module-tier): it writes a
//! polymorphic function type, or names `Lazy`. A module that only passes an argument to a parameter
//! of a polymorphic function type that another module declares writes none, and stays in core, as
//! does one that calls itself at other types (polymorphism.recursion).

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::body_starts;
use stilt_hir::decls::{FnSig, TypeDefInfo, declarations};
use stilt_hir::hir;
use stilt_hir::module_hir;

use crate::queries::{infer_body, module_info};
use crate::tast::walk;
use crate::tast::{Code, Definition, StmtKind, TypedBody};
use crate::ty::Ty;

/// Whether a file's module writes a polymorphic function type, anywhere, or names `Lazy` in a
/// declaration's types or in a value its code makes or binds.
///
/// # Panics
///
/// If the module has 4G bodies or more.
#[must_use]
pub fn uses_polymorphism(db: &dyn Db, program: Program, file: SourceFile) -> bool {
    if !module_hir(db, program, file).poly_names.is_empty() {
        return true;
    }
    let module = &module_info(db, program, file).name;
    let bodies = u32::try_from(body_starts(db, program, file).len()).expect("under 4G bodies");
    declares_lazy(db, program, module)
        || (0..bodies).any(|i| {
            let expansions = &stilt_hir::module_body(db, program, file, i).expansions;
            holds_lazy(&infer_body(db, program, file, i).body, expansions)
        })
}

/// Whether the declarations of `module` name `Lazy` in their types.
fn declares_lazy(db: &dyn Db, program: Program, module: &str) -> bool {
    let decls = declarations(db, program);
    let sig = |s: &FnSig| {
        s.params.iter().any(|(_, t)| names(t))
            || names(&s.ret)
            || s.row.raise.as_deref().is_some_and(names)
    };
    let types = decls.types.iter().any(|(item, info)| {
        &*item.home == module
            && match &info.def {
                TypeDefInfo::Record(fields) => fields.iter().any(|(_, t)| names(t)),
                TypeDefInfo::Variants(vs) => vs.iter().flat_map(|(_, ts)| ts).any(names),
                TypeDefInfo::Builtin => false,
            }
    });
    let functions = decls
        .functions
        .iter()
        .any(|(item, s)| &*item.home == module && sig(s));
    let members = decls
        .inherent
        .iter()
        .filter(|(owner, _)| &*owner.home == module)
        .any(|(_, ms)| ms.iter().any(|m| sig(&m.signature)));
    let impls = decls
        .trait_impls
        .values()
        .filter(|i| &*i.module == module)
        .any(|i| i.members.iter().any(|m| sig(&m.signature)));
    types || functions || members || impls
}

/// Whether `item` is `std.lazy`'s `Lazy`.
fn is_lazy(item: &hir::Item) -> bool {
    &*item.home == "std.lazy" && &*item.name == "Lazy"
}

/// Whether a declaration's type names `Lazy`.
fn names(t: &hir::Ty) -> bool {
    match t {
        hir::Ty::Con(item, ts) => is_lazy(item) || ts.iter().any(names),
        hir::Ty::Tuple(ts) | hir::Ty::App(_, ts) => ts.iter().any(names),
        hir::Ty::Fn(f) => {
            f.params.iter().any(|(_, t)| names(t))
                || f.ret.iter().chain(f.row.raise.as_deref()).any(names)
        }
        hir::Ty::Spread(_, t) => names(t),
        hir::Ty::Param(_)
        | hir::Ty::Handler(_)
        | hir::Ty::SelfTy
        | hir::Ty::Value(_)
        | hir::Ty::Error => false,
    }
}

/// Whether a typed body makes or binds a value whose type names `Lazy`.
fn holds_lazy(body: &TypedBody, expansions: &[stilt_hir::hir::Expansion]) -> bool {
    // Nothing in a macro's expansion, fragments included, counts (macros.advanced-tier).
    let ours = |at| !super::in_expansion(expansions, at);
    let mut found = false;
    let mut stmt = |s: &crate::tast::Stmt| {
        if let StmtKind::Let(b) | StmtKind::Var(b) = &s.kind
            && ours(b.pattern.at)
        {
            found |= mentions(&b.pattern.ty);
        }
    };
    let mut expr_found = false;
    let mut expr = |e: &crate::tast::Expr| expr_found |= ours(e.at) && mentions(&e.ty);
    match &body.code {
        Definition::Code(Code::Block(b)) => walk::iter_block(b, &mut stmt, &mut expr),
        Definition::Code(Code::Expr(e)) => walk::iter(e, &mut stmt, &mut expr),
        Definition::Native | Definition::Broken => {}
    }
    found || expr_found
}

/// Whether a type names `Lazy`.
fn mentions(t: &Ty) -> bool {
    match t {
        Ty::Con(item, ts) => is_lazy(item) || ts.iter().any(mentions),
        Ty::Tuple(ts) | Ty::App(_, ts) => ts.iter().any(mentions),
        Ty::Fn(f) => {
            f.params.iter().any(|(_, t)| mentions(t))
                || mentions(&f.ret)
                || f.row.raise.as_deref().is_some_and(mentions)
        }
        Ty::Spread(s) => mentions(&s.elem),
        Ty::Param(_) | Ty::Handler(_) | Ty::SelfTy | Ty::Var(_) | Ty::Value(_) | Ty::Error => false,
    }
}
