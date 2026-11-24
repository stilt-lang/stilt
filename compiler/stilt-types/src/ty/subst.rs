//! Substitution: types for type parameters and `Self`, and rows for row variables, which
//! expands each spread whose pack it replaces with a tuple (variadics.type-spreads).

use stilt_hir::hir::GenericId;

use super::{FnTy, Row, RowParam, Table, Tail, Ty, apply};

/// A substitution of types for type parameters and `Self`, and of rows for row variables.
#[derive(Clone, Debug, Default)]
pub struct Subst {
    /// The type that `Self` stands for.
    pub self_ty: Option<Ty>,
    /// The type each type parameter stands for.
    pub types: Vec<(GenericId, Ty)>,
    /// The row each row variable stands for.
    pub rows: Vec<(RowParam, Row)>,
}

impl Subst {
    /// The substitution that leaves the type parameter `of` as it is, if there is one.
    #[must_use]
    pub fn without(&self, of: Option<&GenericId>) -> Self {
        let mut s = self.clone();
        if let Some(of) = of {
            s.types.retain(|(q, _)| q != of);
        }
        s
    }
}

impl Table {
    /// Replaces type parameters, `Self` and row parameters.
    #[must_use]
    pub fn subst(&self, s: &Subst, t: &Ty) -> Ty {
        match self.resolve(t) {
            Ty::Con(item, args) => Ty::Con(
                item.clone(),
                args.iter().map(|a| self.subst(s, a)).collect(),
            ),
            Ty::Param(p) => s
                .types
                .iter()
                .find(|(q, _)| q == p)
                .map_or_else(|| Ty::Param(p.clone()), |(_, t)| t.clone()),
            Ty::SelfTy => s.self_ty.clone().unwrap_or(Ty::SelfTy),
            Ty::Value(_) => t.clone(),
            Ty::App(head, ts) => apply(
                self.subst(s, head),
                ts.iter().map(|t| self.subst(s, t)).collect(),
            ),
            Ty::Tuple(ts) => {
                Ty::Tuple(self.expand(ts, &mut |t, p| t.subst(s, p), &mut |t, x, of| {
                    t.subst(&s.without(of), x)
                }))
            }
            Ty::Spread(sp) => Ty::spread(
                self.subst(s, &sp.pack),
                sp.of.clone(),
                self.subst(&s.without(Some(&sp.of)), &sp.elem),
            ),
            Ty::Fn(f) => Ty::Fn(Box::new(FnTy {
                generics: f.generics.clone(),
                bound_args: f.bound_args_with(|a| self.subst(s, a)),
                params: self.expand_params(
                    &f.params,
                    &mut |t, p| t.subst(s, p),
                    &mut |t, x, of| t.subst(&s.without(of), x),
                ),
                ret: self.subst(s, &f.ret),
                row: self.subst_row(s, &f.row),
            })),
            Ty::Handler(h) => Ty::Handler(Box::new(super::HandlerTy {
                effect: h.effect.clone(),
                args: h.args.iter().map(|a| self.subst(s, a)).collect(),
                answer: h.answer.as_ref().map(|a| self.subst(s, a)),
                row: self.subst_row(s, &h.row),
            })),
            t @ (Ty::Var(_) | Ty::Error) => t.clone(),
        }
    }

    /// A row with its raise substituted, and each row parameter that the substitution replaces
    /// replaced, the replacements' labels joining the row's. At most one row parameter of the
    /// row may be replaced by a row that ends in an open row: a use joins the open rows that
    /// stand for a signature's own row variables into one (effects.non-escaping-parameters).
    ///
    /// # Panics
    ///
    /// If two row parameters of the row are replaced by rows that end in open rows.
    #[must_use]
    pub fn subst_row(&self, s: &Subst, r: &Row) -> Row {
        let mut out = Row {
            raise: r.raise.as_ref().map(|t| Box::new(self.subst(s, t))),
            effects: r
                .effects
                .iter()
                .map(|(e, args)| (e.clone(), args.iter().map(|a| self.subst(s, a)).collect()))
                .collect(),
            tail: Tail::Closed,
            ..r.clone()
        };
        let mut params = Vec::new();
        let mut open = None;
        for p in r.tail.params() {
            match s.rows.iter().find(|(q, _)| q == p) {
                Some((_, replacement)) => {
                    out = out.merge_labels(replacement);
                    match &replacement.tail {
                        Tail::Var(rv) => {
                            assert!(open.is_none(), "a row joins one open row at most");
                            open = Some(*rv);
                        }
                        tail => params.extend_from_slice(tail.params()),
                    }
                }
                None => params.push(p.clone()),
            }
        }
        out.tail = match (open, &r.tail) {
            (_, Tail::Var(rv)) => Tail::Var(*rv),
            (Some(rv), _) => {
                assert!(
                    params.is_empty(),
                    "a row holds an open row or row parameters"
                );
                Tail::Var(rv)
            }
            (None, _) => Tail::of_params(params),
        };
        out
    }
}
