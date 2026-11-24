//! Value parameters that a call can find (generics.value-parameters-determined): each appears in a
//! parameter's type or in the result type, outside every row, or is E0346.

use stilt_diag::codes;
use stilt_syntax::SyntaxKind;
use stilt_syntax::ast::{self, AstNode};

use super::{Ctx, Resolver};
use crate::hir::{GenericId, Param, Ty};

impl Resolver<'_> {
    /// generics.value-parameters-determined: each value parameter of a function appears in the type
    /// of one of its parameters or in its result type, outside every row, which alone give it a
    /// value at a call, or is E0346 at the parameter.
    pub(super) fn check_determined(
        &mut self,
        (signature, f): (&Ctx, &ast::Fn),
        owner: &crate::hir::Owner,
        params: &[Param],
        ret: Option<&Ty>,
    ) {
        let written: Vec<ast::Generic> = f
            .generic_list()
            .iter()
            .flat_map(ast::GenericList::generics)
            .collect();
        for (index, g) in (0..).zip(&written) {
            let ast::Generic::ValueParam(p) = g else {
                continue;
            };
            let id = GenericId {
                owner: owner.clone(),
                index,
            };
            // One whose name another generic took first is no parameter, which E0208 reports,
            // and one whose type is an error stands nowhere as a value (errors.error-type).
            match signature.value_params.iter().find(|(_, g, _)| *g == id) {
                Some((_, _, t)) if *t != Ty::Error => {}
                _ => continue,
            }
            let typed = params.iter().filter_map(|p| match p {
                Param::Param(_, t, _) => Some(t),
                Param::SelfParam(_, t) => t.as_ref(),
            });
            if typed.chain(ret).any(|t| appears(t, &id)) {
                continue;
            }
            let n = self.name(p.name(), p.syntax());
            // A type that failed to resolve may hold it where it is written, so no diagnostic
            // arises from that type (errors.error-type, "The error type").
            if in_an_error(f, (params, ret), &n.name) {
                continue;
            }
            let message = format!(
                "`{}` appears in no parameter's type and not in the result type, so no call \
                 determines it",
                n.name
            );
            self.error(codes::E0346, self.at(p.syntax()), message);
        }
    }
}

/// Whether a type names the generic `id` outside every row (generics.value-parameters-determined).
fn appears(t: &Ty, id: &GenericId) -> bool {
    match t {
        Ty::Param(p) => p == id,
        Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().any(|t| appears(t, id)),
        Ty::App(head, ts) => appears(head, id) || ts.iter().any(|t| appears(t, id)),
        Ty::Fn(f) => {
            f.params.iter().any(|(_, t)| appears(t, id))
                || f.ret.as_ref().is_some_and(|t| appears(t, id))
        }
        Ty::Spread(_, t) => appears(t, id),
        Ty::Handler(h) => {
            h.effect.args.iter().any(|t| appears(t, id))
                || h.answer.as_ref().is_some_and(|t| appears(t, id))
        }
        Ty::SelfTy | Ty::Value(_) | Ty::Error => false,
    }
}

/// Whether `name` is written in a parameter's type or the result type whose type has the error
/// type in it, where it may stand.
fn in_an_error(f: &ast::Fn, (params, ret): (&[Param], Option<&Ty>), name: &str) -> bool {
    let written = f
        .param_list()
        .into_iter()
        .flat_map(|l| l.params())
        .map(|p| p.ty());
    let typed = params.iter().filter_map(|p| match p {
        Param::Param(_, t, _) => Some(t),
        Param::SelfParam(..) => None,
    });
    let result = (ret, f.ret_type().and_then(|r| r.ty()));
    typed
        .zip(written)
        .chain(result.0.map(|t| (t, result.1)))
        .any(|(t, w)| has_error(t) && w.is_some_and(|w| written_in(&w, name)))
}

/// Whether a type has the error type in it, outside every row.
fn has_error(t: &Ty) -> bool {
    match t {
        Ty::Error => true,
        Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().any(has_error),
        Ty::App(head, ts) => has_error(head) || ts.iter().any(has_error),
        Ty::Fn(f) => {
            f.params.iter().any(|(_, t)| has_error(t)) || f.ret.as_ref().is_some_and(has_error)
        }
        Ty::Spread(_, t) => has_error(t),
        Ty::Handler(h) => {
            h.effect.args.iter().any(has_error) || h.answer.as_ref().is_some_and(has_error)
        }
        Ty::Param(_) | Ty::SelfTy | Ty::Value(_) => false,
    }
}

/// Whether `name` is written in `ty` as a type of one name, outside every row and the type
/// parameters of a polymorphic function type.
fn written_in(ty: &ast::Type, name: &str) -> bool {
    let mut nodes = vec![ty.syntax().clone()];
    while let Some(node) = nodes.pop() {
        if matches!(node.kind(), SyntaxKind::ROW | SyntaxKind::GENERIC_LIST) {
            continue;
        }
        if let Some(named) = ast::NamedType::cast(node.clone()) {
            let segments: Vec<_> = named.path().iter().flat_map(ast::Path::segments).collect();
            if let [one] = segments.as_slice()
                && one.text() == name
            {
                return true;
            }
        }
        nodes.extend(node.children());
    }
    false
}
