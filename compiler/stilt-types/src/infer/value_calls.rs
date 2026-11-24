//! Calls of a variant, which constructs it, and of a function value.

use stilt_diag::codes;
use stilt_hir::hir::{self, Arg, Item, Mode};
use stilt_syntax::TextRange;

use super::calls::arg_mode;
use super::exprs::is_spread;
use super::{Cx, State, error_node, node};
use crate::tast;
use crate::ty::{Ty, instantiate};

impl State<'_> {
    /// A variant applied to its payload.
    pub(super) fn variant_call(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        callee: &hir::Expr,
        item: &Item,
        args: &[Arg],
    ) -> tast::Expr {
        let Some(v) = self.env.decls.variant(item) else {
            return error_node(at);
        };
        if v.payload.is_empty() {
            // declarations.constructors: a variant without a payload is a value.
            let message = format!(
                "`{}` has no payload, so it is written without parentheses",
                item.name
            );
            self.error(codes::E0311, callee.at, message);
            for a in args {
                self.abandon(cx, &a.value);
            }
            return error_node(at);
        }
        let (ty, targs, params) = self.instantiate_type(callee.at, &v.ty);
        let payload: Vec<(Mode, Ty)> = v
            .payload
            .iter()
            .map(|t| (Mode::Let, instantiate(t, &params, &targs)))
            .collect();
        let values = self
            .arguments(cx, at, &payload, &[], args)
            .into_iter()
            .map(|a| a.value)
            .collect();
        node(
            tast::ExprKind::Construct(item.clone(), targs, values),
            ty,
            at,
        )
    }

    /// A call of a function value.
    pub(super) fn value_call(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        callee: &hir::Expr,
        args: &[Arg],
    ) -> tast::Expr {
        let f = self.infer(cx, None, callee);
        let resolved = self.resolved(&f.ty);
        // A callee whose type is unknown takes the arguments' types, a spread's among them.
        let open = matches!(resolved, Ty::Var(_)) && args.iter().any(|a| is_spread(&a.value));
        let fty = match resolved {
            Ty::Fn(fty) => *fty,
            Ty::Var(_) => {
                let params: Vec<(Mode, Ty)> = args
                    .iter()
                    .map(|a| (arg_mode(a), self.fresh(a.value.at)))
                    .collect();
                let ret = self.fresh(at);
                let row = self.table.fresh_row(false);
                let expected = Ty::func(params.clone(), ret.clone(), row.clone());
                self.expect(callee.at, &expected, &f.ty);
                crate::ty::FnTy {
                    generics: Vec::new(),
                    bound_args: Vec::new(),
                    params,
                    ret,
                    row,
                }
            }
            Ty::Error => return self.give_up(cx, at, args),
            t => {
                let message = format!("expected a function, found `{}`", self.show(&t));
                self.error(codes::E0311, callee.at, message);
                return self.give_up(cx, at, args);
            }
        };
        let params = self.table.fit_params(&fty.params, args.len());
        let call_args = if open {
            self.open_spread_arguments(cx, at, &params, args)
        } else {
            self.arguments(cx, at, &params, &[], args)
        };
        self.perform_call(cx, fty.row, at);
        node(
            tast::ExprKind::CallValue(Box::new(f), call_args),
            fty.ret,
            at,
        )
    }
}
