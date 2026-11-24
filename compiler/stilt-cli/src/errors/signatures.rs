//! The bodies whose signatures meet the error type (program.meeting-the-error-type): a parameter,
//! return or raise type, or a bound, that holds an error, or for a method, its impl's type, trait
//! or bounds. Such an error lies in the declaration, or comes from a name with an error elsewhere.

use stilt_hir::hir::{
    DeclKind, FnBody, FnDecl, Generic, GenericKind, ItemHir, MemberKind, ModuleHir, Param, TraitRef,
};
use stilt_types::hir_holds_error;

use super::BodySet;

/// The bodies of a module whose signatures, or whose impls' headers, hold the error type.
pub(super) fn signature_errors(module: &ModuleHir) -> BodySet {
    let mut found = BodySet::new();
    for item in &module.items {
        match item {
            ItemHir::Use => {}
            ItemHir::Decl(d) => match &d.kind {
                DeclKind::Fn(f) => add_fn(&mut found, f, false),
                DeclKind::Const(c) => {
                    if hir_holds_error(&c.ty) {
                        found.insert(c.value.0);
                    }
                }
                DeclKind::Trait(t) => {
                    for m in &t.members {
                        match &m.kind {
                            MemberKind::Fn(f) => add_fn(&mut found, f, false),
                            MemberKind::TraitConst(_, ty, Some(value)) if hir_holds_error(ty) => {
                                found.insert(value.0);
                            }
                            MemberKind::TraitConst(..) | MemberKind::Const(_) => {}
                        }
                    }
                }
                DeclKind::Type(_)
                | DeclKind::Test(..)
                | DeclKind::Macro(_)
                | DeclKind::Effect(_) => {}
            },
            ItemHir::Impl(block) => {
                let header = hir_holds_error(&block.self_ty)
                    || block.trait_ref == Some(TraitRef::Error)
                    || bounds_have_error(&block.generics);
                for m in &block.members {
                    match &m.kind {
                        MemberKind::Fn(f) => add_fn(&mut found, f, header),
                        MemberKind::Const(c) => {
                            if header || hir_holds_error(&c.ty) {
                                found.insert(c.value.0);
                            }
                        }
                        MemberKind::TraitConst(..) => {}
                    }
                }
            }
        }
    }
    found
}

/// Adds a function's body if its signature, or the header around it, holds the error type.
fn add_fn(found: &mut BodySet, f: &FnDecl, header: bool) {
    let Some(FnBody::Block(body) | FnBody::Hole(body)) = f.body else {
        return;
    };
    let params = f.params.iter().any(|p| match p {
        Param::Param(_, t, _) => hir_holds_error(t),
        Param::SelfParam(_, t) => t.as_ref().is_some_and(hir_holds_error),
    });
    let ret = f.ret.as_ref().is_some_and(hir_holds_error);
    let raise = f.row.raise.as_deref().is_some_and(hir_holds_error);
    if header || params || ret || raise || bounds_have_error(&f.generics) {
        found.insert(body.0);
    }
}

/// Whether a bound of a list of generics has an error.
fn bounds_have_error(generics: &[Generic]) -> bool {
    generics.iter().any(|g| match &g.kind {
        GenericKind::Type(bounds) => bounds.contains(&TraitRef::Error),
        GenericKind::Value(t) => *t == stilt_hir::hir::Ty::Error,
        GenericKind::Row => false,
    })
}
