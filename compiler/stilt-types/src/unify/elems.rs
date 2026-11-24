//! Unification of the elements of tuple types and of function types' parameters, which may
//! spread packs (variadics.type-spreads and variadics.pack-inference).

use stilt_hir::hir::Mode;
use stilt_syntax::TextRange;

use crate::ty::{Kind, Spread, Table, Ty, replace};

impl Table {
    /// Makes two lists of elements one: their plain elements before and after their spreads
    /// pairwise, and what lies between, a spread of one pack on each side, or a spread whose
    /// pack is a variable on one side and any elements on the other, which solve the variable,
    /// as a tuple argument gives a pack its elements.
    pub fn unify_elems(&mut self, xs: &[Ty], ys: &[Ty]) -> bool {
        let xs = self.elements(xs);
        let ys = self.elements(ys);
        let spread = |t: &Ty| t.as_spread().is_some();
        if !xs.iter().any(spread) && !ys.iter().any(spread) {
            return xs.len() == ys.len() && xs.iter().zip(&ys).all(|(x, y)| self.unify(x, y));
        }
        let plain = |(x, y): &(&Ty, &Ty)| !spread(x) && !spread(y);
        let front = xs.iter().zip(&ys).take_while(plain).count();
        let back = xs[front..]
            .iter()
            .rev()
            .zip(ys[front..].iter().rev())
            .take_while(plain)
            .count();
        for i in 0..front {
            if !self.unify(&xs[i], &ys[i]) {
                return false;
            }
        }
        for i in 1..=back {
            if !self.unify(&xs[xs.len() - i], &ys[ys.len() - i]) {
                return false;
            }
        }
        self.unify_middle(&xs[front..xs.len() - back], &ys[front..ys.len() - back])
    }

    /// Makes the elements between two lists' plain ends one.
    fn unify_middle(&mut self, mx: &[Ty], my: &[Ty]) -> bool {
        match (mx, my) {
            ([], []) => true,
            ([Ty::Spread(a)], [Ty::Spread(b)]) if self.same_pack(&a.pack, &b.pack) => {
                let renamed = replace(&b.elem, &b.of, &Ty::Param(a.of.clone()));
                self.unify(&a.elem, &renamed)
            }
            ([Ty::Spread(a)], m) | (m, [Ty::Spread(a)]) if self.unsolved(&a.pack).is_some() => {
                self.solve_pack(a, m)
            }
            // Otherwise one for one, where a spread meets only the error type, which meets
            // every type (errors.error-type).
            _ => mx.len() == my.len() && mx.iter().zip(my).all(|(x, y)| self.unify(x, y)),
        }
    }

    /// Whether two packs are the same: one type parameter, or one variable.
    fn same_pack(&self, a: &Ty, b: &Ty) -> bool {
        match (self.resolve(a), self.resolve(b)) {
            (Ty::Var(x), Ty::Var(y)) => x == y,
            (Ty::Param(p), Ty::Param(q)) => p == q,
            _ => false,
        }
    }

    /// Solves the variable that is the pack of `s` with the elements `middle`: one element
    /// for each, whose type makes `s`'s element type that element's, and a spread of another
    /// pack for each spread among them, which keeps that pack's elements in place.
    fn solve_pack(&mut self, s: &Spread, middle: &[Ty]) -> bool {
        let mut seq = Vec::new();
        for m in middle {
            let w = self.fresh(Kind::Any, TextRange::default());
            let pattern = replace(&s.elem, &s.of, &w);
            let (target, element) = match m {
                Ty::Spread(inner) => (
                    &inner.elem,
                    Ty::spread(inner.pack.clone(), inner.of.clone(), w),
                ),
                m => (m, w),
            };
            if !self.unify(&pattern, target) {
                return false;
            }
            seq.push(element);
        }
        if self.unsolved(&s.pack).is_none() || self.occurs_any(&s.pack, &seq) {
            return false;
        }
        self.solve(&s.pack, Ty::Tuple(seq));
        true
    }

    /// Whether the unsolved variable `v` occurs in any of `ts`.
    fn occurs_any(&self, v: &Ty, ts: &[Ty]) -> bool {
        self.unsolved(v)
            .is_some_and(|info| ts.iter().any(|t| self.occurs(info.id, t)))
    }

    /// Whether the parameters of two function types, whose elements are one, have the same
    /// modes, each spread's elements taken by value.
    pub(crate) fn same_modes(&self, ps: &[(Mode, Ty)], qs: &[(Mode, Ty)]) -> bool {
        let ps = self.expand_params(ps, &mut |_, p| p.clone(), &mut |_, t, _| t.clone());
        let qs = self.expand_params(qs, &mut |_, p| p.clone(), &mut |_, t, _| t.clone());
        ps.len() == qs.len() && ps.iter().zip(&qs).all(|((m, _), (n, _))| m == n)
    }

    /// The parameters of a function type, its spreads whose packs are solved expanded, and a
    /// spread whose pack is a variable solved with as many elements as make `n` parameters,
    /// as a closure's arity gives them (variadics.pack-inference).
    pub fn fit_params(&mut self, params: &[(Mode, Ty)], n: usize) -> Vec<(Mode, Ty)> {
        let same = |_: &Self, t: &Ty| t.clone();
        let elements = self.expand_params(params, &mut |_, p| p.clone(), &mut |t, x, _| same(t, x));
        let open: Vec<Spread> = elements
            .iter()
            .filter_map(|(_, t)| t.as_spread())
            .filter(|s| self.unsolved(&s.pack).is_some())
            .cloned()
            .collect();
        let [s] = open.as_slice() else {
            return elements;
        };
        let Some(count) = (n + 1).checked_sub(elements.len()) else {
            return elements;
        };
        let seq: Vec<Ty> = (0..count)
            .map(|_| self.fresh(Kind::Any, TextRange::default()))
            .collect();
        self.solve(&s.pack, Ty::Tuple(seq));
        self.expand_params(&elements, &mut |_, p| p.clone(), &mut |t, x, _| same(t, x))
    }
}
