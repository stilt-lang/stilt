//! Values of polymorphic function types (polymorphism.instantiation and polymorphism.rigid-types).
//!
//! Such a value is a closure, whose code takes, after the closure, a witness for each of its
//! type parameters and a dictionary for each of its bounds, as a generic function takes them
//!, then its arguments. Its code is compiled once, and holds a value of each
//! type parameter in one word, whose heapness the witness tells: a call at a type argument of
//! several words passes it in its box, as a call past the caps of instances does
//! (`super::bridge`), converting the arguments in and the result and the error back. A generic
//! function named where such a type is expected, and a value of one used as a value of a
//! monomorphic function type, are closures whose code makes the call.

use stilt_hir::hir::{GenericId, LocalId};
use stilt_types::tast::{self, Arg as TArg, Callee as TCallee, Expr, ExprKind, Pat, PatKind};
use stilt_types::ty::{FnTy, Subst, Table, Ty};

use super::Lower;
use super::bridge::{Bridged, Dir, Given};
use crate::Held;
use crate::mir::{Arg, Operand, ParamMode, Repr};

impl Lower<'_> {
    /// Brings the type parameters of the polymorphic function type `fty` into the scope of the
    /// code of a closure of it, each with the witness and the dictionaries that its next
    /// parameters hold, and held in one word.
    pub(crate) fn poly_params(&mut self, fty: &FnTy) {
        for (g, bounds) in &fty.generics {
            let witness = self.b.param(Repr::Scalar, ParamMode::Borrowed, None);
            let dicts = bounds
                .iter()
                .map(|t| {
                    let d = self.b.param(Repr::Heap, ParamMode::Borrowed, None);
                    (t.clone(), Operand::Local(d))
                })
                .collect();
            self.push_generic(Ty::Param(g.clone()), witness, dicts, Some(&Held::Word));
        }
        // The arguments its bounds give traits with parameters (traits.bound-arguments).
        for (g, t, args) in &fty.bound_args {
            self.bound_args
                .push((Ty::Param(g.clone()), t.clone(), args.clone()));
        }
    }

    /// A call of `value`, of a polymorphic function type, at the type arguments `targs`, with
    /// the arguments `args`: each type argument is passed with its witness and
    /// dictionaries, and in its box if it has several words.
    pub(crate) fn call_poly(
        &mut self,
        value: &Expr,
        targs: &[Ty],
        args: &[TArg],
        call: &Expr,
    ) -> Vec<Operand> {
        let Ty::Fn(poly) = &value.ty else {
            unreachable!("only a function is instantiated")
        };
        let closure = self.expr1(value);
        let given: Vec<Given> = args
            .iter()
            .map(|a| match a.mode {
                stilt_hir::hir::Mode::Let => Given::Let(self.expr(&a.value)),
                stilt_hir::hir::Mode::Inout => Given::Place(self.place(&a.value)),
            })
            .collect();
        let (start, crossed) = (self.generics.len(), self.crossing.len());
        let held: Vec<Ty> = targs
            .iter()
            .map(|a| {
                if self.one_word(a) {
                    a.clone()
                } else {
                    self.crossing_for(a.clone())
                }
            })
            .collect();
        let mut hidden = Vec::new();
        for ((_, bounds), ty) in poly.generics.iter().zip(&held) {
            hidden.push(Arg::Borrow(self.witness(ty)));
            for t in bounds {
                hidden.push(Arg::Borrow(self.dict(ty, t)));
            }
        }
        let params: Vec<GenericId> = poly.generics.iter().map(|(g, _)| g.clone()).collect();
        let outside = |t: &Ty| at_types(&params, targs, t);
        let inside = |t: &Ty| at_types(&params, &held, t);
        let args = given
            .into_iter()
            .zip(&poly.params)
            .map(|(g, (_, t))| (g, outside(t), inside(t)))
            .collect();
        let errs = poly.row.raise.as_deref().map(|t| (outside(t), inside(t)));
        let loc = self.loc_at(call.at);
        let ret = (&call.ty, &inside(&poly.ret));
        let bridged = Bridged::Closure(closure, hidden);
        let out = self.bridged_call(bridged, args, Dir::In, ret, errs, loc);
        self.undemote(start, crossed);
        out
    }

    /// A generic function named where a polymorphic function type is expected
    /// (polymorphism.arguments): a closure whose code calls it at the type arguments `targs`, which
    /// name the type's parameters.
    pub(crate) fn poly_function_value(
        &mut self,
        callee: &TCallee,
        targs: &[Ty],
        e: &Expr,
    ) -> Operand {
        let Ty::Fn(p) = &e.ty else {
            unreachable!("a polymorphic value is a function")
        };
        let (params, args) = self.forwarded(p, e);
        let body = Expr {
            kind: ExprKind::Call(callee.clone(), targs.to_vec(), args, p.row.clone()),
            ty: p.ret.clone(),
            at: e.at,
        };
        self.closure(&params, &body, e)
    }

    /// A value of a polymorphic function type instantiated at `targs` and used as a value of the
    /// monomorphic function type `e`'s (polymorphism.instantiation): a closure whose code calls it
    /// there. The value is a local or a field of one, which the closure reads when it is called.
    pub(crate) fn instantiated_value(&mut self, f: &Expr, targs: &[Ty], e: &Expr) -> Operand {
        let Ty::Fn(m) = &e.ty else {
            unreachable!("an instantiation is a function")
        };
        let (params, args) = self.forwarded(m, e);
        let callee = Expr {
            kind: ExprKind::Instantiate(Box::new(f.clone()), targs.to_vec()),
            ty: e.ty.clone(),
            at: e.at,
        };
        let body = Expr {
            kind: ExprKind::CallValue(Box::new(callee), args),
            ty: m.ret.clone(),
            at: e.at,
        };
        self.closure(&params, &body, e)
    }

    /// The parameters of a closure of type `fty` made at `e`, each bound to a local of its own,
    /// and the arguments that pass them on.
    fn forwarded(&mut self, fty: &FnTy, e: &Expr) -> (Vec<Pat>, Vec<TArg>) {
        fty.params
            .iter()
            .map(|(mode, ty)| {
                let id = LocalId(u32::try_from(self.names.len()).expect("under 4G locals"));
                self.names.push("#forwarded".into());
                let pat = Pat {
                    kind: PatKind::Bind(id),
                    ty: ty.clone(),
                    at: e.at,
                };
                let arg = tast::Arg {
                    mode: *mode,
                    value: Expr {
                        kind: ExprKind::Local(id),
                        ty: ty.clone(),
                        at: e.at,
                    },
                    passes: false,
                    kept: false,
                };
                (pat, arg)
            })
            .unzip()
    }
}

/// The type `t` with the type parameters `params` replaced by `args`.
fn at_types(params: &[GenericId], args: &[Ty], t: &Ty) -> Ty {
    let s = Subst {
        types: params.iter().cloned().zip(args.iter().cloned()).collect(),
        ..Subst::default()
    };
    Table::default().subst(&s, t)
}
