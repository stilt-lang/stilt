//! The types of a body: the signatures it instantiates, and the types it writes and names.

use stilt_hir::decls::FnSig;
use stilt_hir::hir::{self, GenericId, Item, Mode, TypeRef};
use stilt_syntax::TextRange;

use super::State;
use crate::tast::Label;
use crate::ty::{Passing, Row, RowParam, Subst, Ty};

/// A signature in the types of type checking, where each non-escaping parameter's type and the
/// function's own row hold the parameter's implicit row variable (effects.non-escaping-parameters).
#[derive(Clone, Debug)]
pub(super) struct Sig {
    pub(super) type_params: Vec<(GenericId, Vec<Item>)>,
    /// The arguments its bounds give traits with parameters (traits.bound-arguments).
    pub(super) bound_args: Vec<(GenericId, Item, Vec<Ty>)>,
    /// Types that stand for some of its parameters at every use: a trait's parameters, which the
    /// receiver's impl or bound gives (traits.trait-arguments), and a constructor trait's `Self`.
    pub(super) fixed: Vec<(GenericId, Ty)>,
    /// Its row variables: the written ones, then the implicit ones.
    pub(super) row_params: Vec<RowParam>,
    pub(super) params: Vec<(Mode, Ty)>,
    /// Whether each parameter passes its argument's effects through.
    pub(super) passing: Vec<bool>,
    pub(super) ret: Ty,
    /// Whether it is a projection, whose call is a place (projections.call-is-place).
    pub(super) projection: bool,
    pub(super) row: Row,
}

impl Sig {
    /// The signature, where `Self` means `self_ty` if it is given.
    pub(super) fn of(s: &FnSig, self_ty: Option<&Ty>) -> Self {
        let passing = Passing::of(s, self_ty);
        let mut row_params: Vec<RowParam> = s
            .row_params
            .iter()
            .cloned()
            .map(RowParam::Written)
            .collect();
        row_params.extend(passing.implicit);
        Self {
            type_params: s.type_params.clone(),
            bound_args: s
                .bound_args
                .iter()
                .map(|b| {
                    let args = b.args.iter().map(|a| Ty::from_hir(a, self_ty)).collect();
                    (b.param.clone(), b.trait_item.clone(), args)
                })
                .collect(),
            fixed: Vec::new(),
            row_params,
            params: passing.params,
            passing: (0..s.params.len())
                .map(|i| s.passing.get(i).copied().unwrap_or(false))
                .collect(),
            ret: Ty::from_hir(&s.ret, self_ty),
            projection: s.projection,
            row: passing.row,
        }
    }

    /// The packs among its type parameters: those its parameters' types and its result spread
    /// (variadics.packs).
    pub(super) fn packs(&self) -> Vec<GenericId> {
        fn of_ty(acc: &mut Vec<GenericId>, t: &Ty) {
            match t {
                Ty::Spread(s) => {
                    if let Ty::Param(p) = &s.pack {
                        acc.push(p.clone());
                    }
                    of_ty(acc, &s.elem);
                }
                Ty::Fn(f) => {
                    of_ty(acc, &f.ret);
                    f.params.iter().for_each(|(_, t)| of_ty(acc, t));
                }
                Ty::Con(_, args) | Ty::Tuple(args) | Ty::App(_, args) => {
                    for t in args {
                        of_ty(acc, t);
                    }
                }
                Ty::Param(_)
                | Ty::Handler(_)
                | Ty::SelfTy
                | Ty::Var(_)
                | Ty::Value(_)
                | Ty::Error => {}
            }
        }
        let mut acc = Vec::new();
        for (_, t) in &self.params {
            of_ty(&mut acc, t);
        }
        of_ty(&mut acc, &self.ret);
        acc
    }

    /// The signature with the trait's parameters standing for `fixed` (traits.trait-arguments).
    pub(super) fn with_fixed(mut self, fixed: Vec<(GenericId, Ty)>) -> Self {
        self.fixed = fixed;
        self
    }

    /// effects.paired-row-variables: the row variables, written and implicit, that the signature
    /// pairs with an error type, with that type, and effects.passing-to-paired-variables and
    /// effects.what-paired-variable-may-raise as handlers.with-pairing applies them, with each
    /// effect that a row holds beside them. A row of the signature is one of its parameter types'
    /// rows, at any depth, or its own row.
    pub(super) fn pairs(&self) -> Vec<(RowParam, Label)> {
        fn of_ty(acc: &mut Vec<(RowParam, Label)>, t: &Ty) {
            match t {
                Ty::Fn(f) => {
                    of_ty(acc, &f.ret);
                    of_row(acc, &f.row);
                    f.params.iter().for_each(|(_, t)| of_ty(acc, t));
                }
                Ty::Con(_, args) | Ty::Tuple(args) | Ty::App(_, args) => {
                    for t in args {
                        of_ty(acc, t);
                    }
                }
                Ty::Spread(s) => of_ty(acc, &s.elem),
                Ty::Handler(h) => {
                    h.args.iter().chain(&h.answer).for_each(|t| of_ty(acc, t));
                    of_row(acc, &h.row);
                }
                Ty::Param(_) | Ty::SelfTy | Ty::Var(_) | Ty::Value(_) | Ty::Error => {}
            }
        }
        fn of_row(acc: &mut Vec<(RowParam, Label)>, row: &Row) {
            let labels: Vec<Label> = row
                .raise
                .iter()
                .map(|e| Label::Raise((**e).clone()))
                .chain(
                    row.effects
                        .iter()
                        .map(|(e, args)| Label::Effect(e.clone(), args.clone())),
                )
                .collect();
            for v in row.tail.params().iter().rev() {
                for l in labels.iter().rev() {
                    acc.push((v.clone(), l.clone()));
                }
            }
        }
        let mut found = Vec::new();
        of_row(&mut found, &self.row);
        self.params.iter().for_each(|(_, t)| of_ty(&mut found, t));
        found.reverse();
        found
    }
}

/// A signature instantiated at a use: its type arguments, parameters, return type and row, and
/// whether each parameter passes its argument's effects through.
pub(super) struct Instance {
    pub(super) targs: Vec<Ty>,
    pub(super) params: Vec<(Mode, Ty)>,
    pub(super) passing: Vec<bool>,
    pub(super) ret: Ty,
    /// Whether the signature is a projection's (projections.call-is-place).
    pub(super) projection: bool,
    pub(super) row: Row,
}

impl State<'_> {
    /// Instantiates a signature at `at`, with `self_ty` for `Self`. `use_at` is where the use
    /// is reported.
    pub(super) fn instantiate(
        &mut self,
        at: TextRange,
        s: &Sig,
        self_ty: Option<&Ty>,
        use_at: TextRange,
    ) -> Instance {
        let mut types = Vec::new();
        let packs = s.packs();
        for (v, traits) in &s.type_params {
            let m = self.fresh(at);
            // A pack's bounds hold for each of its elements (variadics.packs), and a record
            // bound is met through its fields' types (records.record-bounds).
            let bounded = if packs.contains(v) {
                Ty::spread(m.clone(), v.clone(), Ty::Param(v.clone()))
            } else {
                m.clone()
            };
            for t in traits.iter().filter(|t| !t.is_record_bound()) {
                self.obligation(&bounded, t.clone(), at);
            }
            types.push((v.clone(), m));
        }
        let own = types.len();
        types.extend(s.fixed.iter().cloned());
        let rows: Vec<(RowParam, Row)> = s
            .row_params
            .iter()
            .map(|v| (v.clone(), self.table.fresh_row(false)))
            .collect();
        let sub = Subst {
            self_ty: self_ty.cloned(),
            types,
            rows,
        };
        // traits.bound-arguments: a bound's arguments are those its type's impl gives.
        for (v, t, args) in &s.bound_args {
            let ty = self.table.subst(&sub, &Ty::Param(v.clone()));
            let args = args.iter().map(|a| self.table.subst(&sub, a)).collect();
            self.arg_obligations.push((ty, t.clone(), args, at));
        }
        // effects.passing-to-paired-variables: what the use gives the variables the signature
        // pairs. effects.what-paired-variable-may-raise: what it gives may raise only the paired
        // type.
        for (v, l) in s.pairs() {
            let Some((_, row)) = sub.rows.iter().find(|(w, _)| *w == v) else {
                continue;
            };
            let l = l.map(|t| self.table.subst(&sub, t));
            if let (Label::Raise(raise), Some(rv)) = (&l, self.table.open_var(row)) {
                let mut bound = self.table.fresh_row(false);
                bound.raise = Some(Box::new(raise.clone()));
                self.table
                    .add_upper(rv, (bound, crate::ty::Handled::Nothing));
            }
            self.passed.push((use_at, row.clone(), l));
        }
        let instance = Instance {
            targs: sub.types.iter().take(own).map(|(_, t)| t.clone()).collect(),
            params: s
                .params
                .iter()
                .map(|(m, t)| (*m, self.table.subst(&sub, t)))
                .collect(),
            passing: s.passing.clone(),
            ret: self.table.subst(&sub, &s.ret),
            projection: s.projection,
            row: self.own_row(&sub, &s.row),
        };
        self.taint_broken(&instance);
        instance
    }

    /// Taints the type arguments of an instance whose parameters hold the error type, which
    /// nothing may then decide, so that no use of it is reported (errors.error-type).
    fn taint_broken(&mut self, instance: &Instance) {
        if instance
            .params
            .iter()
            .any(|(_, t)| self.table.mentions_error(t))
        {
            instance.targs.iter().for_each(|t| self.table.taint(t));
        }
    }

    /// A signature's own row as a use instantiates it. Its row variables stand for open rows of
    /// their own, so that each is paired, or not, as the signature says
    /// (effects.passing-to-paired-variables); when it holds several, as it does for a function with
    /// several non-escaping parameters, they are joined into one open row, which grows with each.
    fn own_row(&mut self, sub: &Subst, row: &Row) -> Row {
        if row.tail.params().len() < 2 {
            return self.table.subst_row(sub, row);
        }
        let joined = self.table.fresh_row(false);
        for p in row.tail.params() {
            if let Some((_, r)) = sub.rows.iter().find(|(q, _)| q == p)
                && let Some(rv) = self.table.open_var(r)
            {
                self.table
                    .add_upper(rv, (joined.clone(), crate::ty::Handled::Nothing));
            }
        }
        let labels = Row {
            tail: crate::ty::Tail::Closed,
            ..row.clone()
        };
        let mut out = self.table.subst_row(sub, &labels);
        out.tail = joined.tail;
        out
    }

    /// A type constructor applied to fresh variables, and the variables, with the parameters
    /// the variables stand for.
    pub(super) fn instantiate_type(
        &mut self,
        at: TextRange,
        item: &Item,
    ) -> (Ty, Vec<Ty>, Vec<GenericId>) {
        match self.env.decls.type_info(item) {
            Some(info) => {
                let params = info.params.clone();
                let args: Vec<Ty> = params.iter().map(|_| self.fresh(at)).collect();
                (Ty::Con(item.clone(), args.clone()), args, params)
            }
            None => (Ty::Error, Vec::new(), Vec::new()),
        }
    }

    /// A type written in the body. An error in it is an error of the body (errors.error-type).
    pub(super) fn of_hir(&mut self, t: &TypeRef) -> Ty {
        let ty = Ty::from_hir(&t.ty, self.env.self_ty.as_ref());
        if self.table.mentions_error(&ty) {
            self.broken = true;
        }
        ty
    }

    /// A type named in an expression or a pattern, whose arguments inference supplies
    /// (declarations.type-arguments).
    pub(super) fn named_type(&mut self, t: &TypeRef) -> Ty {
        match &t.ty {
            hir::Ty::Con(item, args) if args.is_empty() => self.instantiate_type(t.at, item).0,
            _ => self.of_hir(t),
        }
    }
}
