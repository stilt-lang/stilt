//! Polymorphic function types (polymorphism.instantiation and polymorphism.rigid-types): a value of
//! one is instantiated afresh at each use that expects no polymorphic type, and an expression given
//! where one is expected is checked with its type parameters as rigid types, which nothing outside
//! it may come to hold.

use stilt_diag::codes;
use stilt_hir::hir::{self, ExprKind, GenericId};
use stilt_syntax::TextRange;

use super::{Cx, State, node};
use crate::tast;
use crate::ty::{FnTy, Subst, Ty};

/// The type parameters of polymorphic function types that a type names, in order and each
/// once.
pub(super) fn rigid_params(t: &Ty, out: &mut Vec<GenericId>) {
    match t {
        Ty::Param(p) if p.is_poly() && !out.contains(p) => out.push(p.clone()),
        Ty::Con(_, ts) | Ty::Tuple(ts) => {
            for t in ts {
                rigid_params(t, out);
            }
        }
        Ty::App(head, ts) => {
            rigid_params(head, out);
            for t in ts {
                rigid_params(t, out);
            }
        }
        Ty::Fn(f) => {
            for (_, t) in &f.params {
                rigid_params(t, out);
            }
            rigid_params(&f.ret, out);
            if let Some(raise) = &f.row.raise {
                rigid_params(raise, out);
            }
            out.retain(|p| f.generics.iter().all(|(g, _)| g != p));
        }
        Ty::Spread(s) => rigid_params(&s.elem, out),
        Ty::Param(_) | Ty::Handler(_) | Ty::SelfTy | Ty::Var(_) | Ty::Value(_) | Ty::Error => {}
    }
}

impl State<'_> {
    /// The names of type parameters, for messages: `` `T` `` or `` `T` and `U` ``.
    pub(super) fn listed(&self, params: &[GenericId]) -> String {
        let names: Vec<String> = params
            .iter()
            .map(|p| format!("`{}`", (self.env.names)(p)))
            .collect();
        match names.as_slice() {
            [] => String::new(),
            [one] => one.clone(),
            [rest @ .., last] => format!("{} and {last}", rest.join(", ")),
        }
    }

    /// A value of a polymorphic function type, used where no polymorphic type is expected: its type
    /// parameters instantiated afresh, each meeting its bounds (polymorphism.instantiation). Any
    /// other value is left as it is.
    pub(super) fn instantiated(&mut self, e: tast::Expr) -> tast::Expr {
        let f = match self.table.resolve(&e.ty) {
            Ty::Fn(f) if f.is_poly() => f.clone(),
            _ => return e,
        };
        let at = e.at;
        let mut types = Vec::new();
        for (g, bounds) in &f.generics {
            let t = self.fresh(at);
            for b in bounds {
                self.obligation(&t, b.clone(), at);
            }
            types.push((g.clone(), t));
        }
        let targs = types.iter().map(|(_, t)| t.clone()).collect();
        let s = Subst {
            types,
            ..Subst::default()
        };
        // Each instantiation's type gives the bounds' traits their arguments
        // (traits.bound-arguments).
        for (g, t, args) in &f.bound_args {
            let ty = self.table.subst(&s, &Ty::Param(g.clone()));
            let args = args.iter().map(|a| self.table.subst(&s, a)).collect();
            self.arg_obligations.push((ty, t.clone(), args, at));
        }
        let ty = self.table.subst(&s, &Ty::Fn(Box::new(f.body())));
        node(tast::ExprKind::Instantiate(Box::new(e), targs), ty, at)
    }

    /// Checks `e` where the polymorphic function type `p` is expected (polymorphism.arguments),
    /// telling whether it fits: a closure literal, whose parameters take the rigid types; a
    /// function named as a value, whose type, instantiated, must be `p`'s with them; or a value of
    /// the same polymorphic type. The rigid types have the bounds `p` gives them.
    pub(super) fn check_poly(
        &mut self,
        cx: &mut Cx,
        p: &FnTy,
        e: &hir::Expr,
    ) -> (tast::Expr, bool) {
        let (expected, p) = &self.own_rigid(p);
        for (g, bounds) in &p.generics {
            self.env.bounds.push((Ty::Param(g.clone()), bounds.clone()));
        }
        // The rigid types give their bounds' traits the arguments written (traits.bound-arguments).
        for (g, t, args) in &p.bound_args {
            let rigid = (Ty::Param(g.clone()), t.clone(), args.clone());
            self.env.bound_args.push(rigid);
        }
        let outer = self.table.var_count();
        let body = Ty::Fn(Box::new(p.body()));
        let (mut v, fits) = match &e.kind {
            ExprKind::Closure(params, b) => {
                let v = self.closure(cx, Some(&body), e.at, params, b);
                let fits = self.fits(e.at, &body, &v.ty);
                (v, fits)
            }
            ExprKind::Func(_) | ExprKind::Member(..) => {
                let v = self.infer(cx, Some(&body), e);
                let fits = self.fits_quietly(&body, &v.ty)
                    || self.not_polymorphic(e.at, (expected, p), &v.ty);
                (v, fits)
            }
            _ => {
                let v = self.infer(cx, Some(expected), e);
                let fits = self.table.unify(&v.ty, expected)
                    || self.not_polymorphic(e.at, (expected, p), &v.ty);
                (v, fits)
            }
        };
        if fits {
            // A closure gives a rigid type away through its body.
            let at = match &e.kind {
                ExprKind::Closure(_, b) => b.at,
                _ => e.at,
            };
            self.keep_rigid(at, outer, p);
            v.ty = expected.clone();
        }
        (v, fits)
    }

    /// E0311 for a value of type `actual` given where the polymorphic function type
    /// `expected`, of parts `p`, is: no type argument of its parameters makes the two equal
    /// (polymorphism.arguments).
    fn not_polymorphic(&mut self, at: TextRange, (expected, p): (&Ty, &FnTy), actual: &Ty) -> bool {
        let params: Vec<GenericId> = p.generics.iter().map(|(g, _)| g.clone()).collect();
        let message = format!(
            "expected `{}`, found `{}`: no type argument of {} makes them equal",
            self.show(expected),
            self.show(actual),
            self.listed(&params),
        );
        self.error(codes::E0311, at, message);
        self.mismatches
            .push((self.errors.len() - 1, expected.clone()));
        false
    }

    /// The polymorphic function type `p` with type parameters of its own: copies of `p`'s, so
    /// that the rigid types of each value checked against it are distinct, and none can have
    /// reached a type before it is checked.
    fn own_rigid(&mut self, p: &FnTy) -> (Ty, FnTy) {
        self.poly_copies += 1;
        let n = self.poly_copies;
        let s = Subst {
            types: p
                .generics
                .iter()
                .map(|(g, _)| (g.clone(), Ty::Param(g.copy(n))))
                .collect(),
            ..Subst::default()
        };
        let Ty::Fn(body) = self.table.subst(&s, &Ty::Fn(Box::new(p.body()))) else {
            unreachable!("a function type stays one")
        };
        let own = FnTy {
            generics: p
                .generics
                .iter()
                .map(|(g, bounds)| (g.copy(n), bounds.clone()))
                .collect(),
            bound_args: p
                .bound_args
                .iter()
                .map(|(g, t, args)| {
                    let args = args.iter().map(|a| self.table.subst(&s, a)).collect();
                    (g.copy(n), t.clone(), args)
                })
                .collect(),
            ..*body
        };
        (Ty::Fn(Box::new(own.clone())), own)
    }

    /// E0311 where a type of the code around a value checked against `p`, one of its first
    /// `outer` variables, came to hold one of `p`'s rigid types, which stand only inside it.
    fn keep_rigid(&mut self, at: TextRange, outer: usize, p: &FnTy) {
        for i in 0..outer {
            let mut found = Vec::new();
            rigid_params(&self.table.freeze(&self.table.var(i)), &mut found);
            found.retain(|g| p.generics.iter().any(|(own, _)| own == g));
            if !found.is_empty() {
                let message = format!(
                    "{} stands for every type the caller picks, so no type outside this value \
                     can be it",
                    self.listed(&found)
                );
                self.error(codes::E0311, at, message);
                return;
            }
        }
    }
}
