//! Unification of types, and of effect rows (effects.inference and effects.function-value-unions).

mod elems;

use stilt_hir::hir::Item;

use crate::ty::{
    FnTy, Handled, HandlerTy, Kind, Row, RowParam, RowState, RowVarId, Subst, Table, Tail, Ty,
    is_float, is_numeric,
};

/// What a row can't hold, of the effects fitted into it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Problem {
    /// `io`, which the row doesn't hold.
    MissingIo,
    /// A raise of this type, where the row raises nothing.
    MissingRaise(Ty),
    /// A raise of the first type, where the row raises the second.
    RaiseMismatch(Ty, Ty),
    /// A written row variable. A non-escaping parameter's implicit one is never missing: it can
    /// reach a row that lacks it only through a use that the parameter's escape reports
    /// (effects.closure-parameters).
    MissingVar(RowParam),
    /// A raise whose type would hold the row itself.
    CyclicRaise(Ty),
    /// An effect the row doesn't hold (handlers.performing-operation).
    MissingEffect(Item),
    /// An effect performed with other type arguments than the row's, or the handler's: the
    /// effect, the arguments given, and those held (handlers.effects-in-rows and handlers.with).
    EffectMismatch(Item, Vec<Ty>, Vec<Ty>),
}

impl Problem {
    /// Whether the problem is one with a user-defined effect (handlers.effects-in-rows and
    /// handlers.performing-operation).
    #[must_use]
    pub fn is_effect(&self) -> bool {
        matches!(
            self,
            Problem::MissingEffect(_) | Problem::EffectMismatch(..)
        )
    }
}

impl Table {
    /// Makes two types one, and tells whether they can be. Meeting the error type taints every
    /// variable on the other side, so that none is reported as unknown (errors.error-type).
    pub fn unify(&mut self, a: &Ty, b: &Ty) -> bool {
        let a = self.shape(a);
        let b = self.shape(b);
        match (&a, &b) {
            (Ty::Error, t) | (t, Ty::Error) => {
                self.taint(t);
                true
            }
            (Ty::Var(_), Ty::Var(_)) => self.unify_vars(&a, &b),
            (Ty::Var(_), t) => self.solve_with(&a, t),
            (t, Ty::Var(_)) => self.solve_with(&b, t),
            (Ty::App(f, xs), Ty::App(g, ys)) => self.unify(f, g) && self.unify_all(xs, ys),
            (Ty::App(f, xs), t) | (t, Ty::App(f, xs)) => self.unify_applied(f, xs, t),
            (Ty::Con(i, xs), Ty::Con(j, ys)) => i == j && self.unify_all(xs, ys),
            (Ty::Param(p), Ty::Param(q)) => p == q,
            // Value arguments are equal by value (generics.equal-types).
            (Ty::Value(x), Ty::Value(y)) => x == y,
            (Ty::SelfTy, Ty::SelfTy) => true,
            (Ty::Tuple(xs), Ty::Tuple(ys)) => self.unify_elems(xs, ys),
            (Ty::Spread(_), Ty::Spread(_)) => {
                self.unify_elems(std::slice::from_ref(&a), std::slice::from_ref(&b))
            }
            (Ty::Fn(f), Ty::Fn(g)) if f.is_poly() || g.is_poly() => self.unify_poly(f, g),
            (Ty::Fn(f), Ty::Fn(g)) if f.has_spread() || g.has_spread() => {
                self.unify_elems(&f.param_types(), &g.param_types())
                    && self.same_modes(&f.params, &g.params)
                    && self.unify(&f.ret, &g.ret)
                    && self.unify_row(&f.row, &g.row)
            }
            (Ty::Fn(f), Ty::Fn(g)) => {
                f.params.len() == g.params.len()
                    && f.params
                        .iter()
                        .zip(&g.params)
                        .all(|((m, x), (n, y))| m == n && self.unify(x, y))
                    && self.unify(&f.ret, &g.ret)
                    && self.unify_row(&f.row, &g.row)
            }
            (Ty::Handler(h), Ty::Handler(k)) => self.unify_handlers(h, k),
            _ => false,
        }
    }

    /// Two handler types, which are one when their effects, arguments, results and rows are
    /// (handlers.handler-literals).
    fn unify_handlers(&mut self, h: &HandlerTy, k: &HandlerTy) -> bool {
        h.effect == k.effect
            && self.unify_all(&h.args, &k.args)
            && match (&h.answer, &k.answer) {
                (None, None) => true,
                (Some(x), Some(y)) => self.unify(x, y),
                _ => false,
            }
            && self.unify_row(&h.row, &k.row)
    }

    /// A constructor applied through the head `f` to `xs`, made one with a type `t` that isn't
    /// applied that way (traits.constructor-parameters). An unsolved head becomes the constructor
    /// at the head of `t`, when `t` applies one to as many arguments. A tuple's or a function's
    /// type becomes the head itself, which has no impl of the trait it is bounded by, so the bound
    /// reports it (E0318); any other type, such as `i64`, or a constructor applied to another
    /// number of arguments, makes no two types equal (E0311).
    fn unify_applied(&mut self, f: &Ty, xs: &[Ty], t: &Ty) -> bool {
        if self.unsolved(f).is_none() {
            return false;
        }
        match t {
            Ty::Con(item, ys) if ys.len() == xs.len() => {
                self.solve(f, Ty::Con(item.clone(), Vec::new()));
                self.unify_all(xs, ys)
            }
            Ty::Tuple(_) | Ty::Fn(_) if !self.occurs_in(f, t) => {
                self.solve(f, t.clone());
                true
            }
            _ => false,
        }
    }

    /// Whether the unsolved variable `f` occurs in `t`.
    fn occurs_in(&self, f: &Ty, t: &Ty) -> bool {
        self.unsolved(f).is_some_and(|v| self.occurs(v.id, t))
    }

    /// Two unsolved variables: the one that may become more types becomes the other.
    fn unify_vars(&mut self, x: &Ty, y: &Ty) -> bool {
        let (Some(vx), Some(vy)) = (self.unsolved(x), self.unsolved(y)) else {
            return false;
        };
        if vx.id == vy.id {
            return true;
        }
        // The more general kind gives way: any type, then any numeric type, then any float.
        let rank = |k| match k {
            Kind::Any => 0,
            Kind::IntLiteral => 1,
            Kind::FloatLiteral => 2,
        };
        if rank(vx.kind) <= rank(vy.kind) {
            self.solve(x, y.clone());
        } else {
            self.solve(y, x.clone());
        }
        true
    }

    /// Solves the unsolved variable `x` with `t`, which isn't a variable, if it may be `t`.
    fn solve_with(&mut self, x: &Ty, t: &Ty) -> bool {
        let Some(v) = self.unsolved(x) else {
            return false;
        };
        let fits = match (v.kind, t) {
            // A variable stands for a monomorphic type only (polymorphism.placement).
            (Kind::Any, _) => !self.occurs(v.id, t) && !t.is_poly(),
            (Kind::IntLiteral, Ty::Con(item, args)) if args.is_empty() => is_numeric(item),
            (Kind::FloatLiteral, Ty::Con(item, args)) if args.is_empty() => is_float(item),
            (Kind::IntLiteral | Kind::FloatLiteral, _) => false,
        };
        if fits {
            self.solve(x, t.clone());
        }
        fits
    }

    /// Two function types of which one is polymorphic: they are the same when they declare as
    /// many type parameters, with the same bounds in the same order, and are equal once `g`'s
    /// are renamed to `f`'s (polymorphism.instantiation).
    fn unify_poly(&mut self, f: &FnTy, g: &FnTy) -> bool {
        if f.generics.len() != g.generics.len()
            || f.generics
                .iter()
                .zip(&g.generics)
                .any(|((_, a), (_, b))| a != b)
        {
            return false;
        }
        let rename = Subst {
            types: g
                .generics
                .iter()
                .zip(&f.generics)
                .map(|((q, _), (p, _))| (q.clone(), Ty::Param(p.clone())))
                .collect(),
            ..Subst::default()
        };
        let same_args = f.bound_args.len() == g.bound_args.len()
            && f.bound_args
                .iter()
                .zip(&g.bound_args)
                .all(|((p, s, xs), (q, t, ys))| {
                    let renamed: Vec<Ty> = ys.iter().map(|y| self.subst(&rename, y)).collect();
                    s == t
                        && Ty::Param(p.clone()) == self.subst(&rename, &Ty::Param(q.clone()))
                        && xs.len() == renamed.len()
                        && xs.iter().zip(&renamed).all(|(x, y)| self.unify(x, y))
                });
        let g = self.subst(&rename, &Ty::Fn(Box::new(g.body())));
        same_args && self.unify(&Ty::Fn(Box::new(f.body())), &g)
    }

    pub(crate) fn unify_all(&mut self, xs: &[Ty], ys: &[Ty]) -> bool {
        xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| self.unify(x, y))
    }

    /// Makes two rows one, as two equal function types need. A least row gains no effect this
    /// way, so it must already hold every effect of the other row (effects.function-value-unions).
    fn unify_row(&mut self, a: &Row, b: &Row) -> bool {
        match (self.open_var(a), self.open_var(b)) {
            (Some(ra), Some(rb)) if ra == rb => true,
            (Some(ra), _) if !self.least(ra) => self.absorb(ra, a, b),
            (_, Some(rb)) if !self.least(rb) => self.absorb(rb, b, a),
            (Some(ra), _) => self.covers(a, b) && self.absorb(ra, a, b),
            (None, Some(rb)) => self.covers(b, a) && self.absorb(rb, b, a),
            (None, None) => {
                let ca = self.row_contents(a);
                let cb = self.row_contents(b);
                self.add(&ca, b).is_empty() && self.add(&cb, a).is_empty()
            }
        }
    }

    /// Makes `m`, which ends in the open row `rv`, and `r` one: `r` must hold what `m` holds,
    /// and `rv` becomes what `r` holds beyond it.
    fn absorb(&mut self, rv: RowVarId, m: &Row, r: &Row) -> bool {
        let contents = self.row_contents(m);
        self.add(&contents, r).is_empty() && self.link(rv, &beyond(r, m))
    }

    /// Whether the row `outer` holds the effects that `inner` holds now. An implicit row
    /// variable needn't be held (see [`Problem::MissingVar`]).
    fn covers(&self, outer: &Row, inner: &Row) -> bool {
        let o = self.row_contents(outer);
        let i = self.row_contents(inner);
        (!i.io || o.io)
            && (i.raise.is_none() || o.raise.is_some())
            && i.effects.iter().all(|(e, _)| o.effect(e).is_some())
            && missing_params(&i.tail, &o.tail).next().is_none()
    }

    /// Makes the open row `rv` the row `r`, which already holds its effects, and moves its
    /// upper bounds to `r`. A row can't hold itself (types.infinite-types).
    fn link(&mut self, rv: RowVarId, r: &Row) -> bool {
        if self.row_mentions(rv, r) {
            return false;
        }
        let uppers = self.uppers(rv);
        self.set_row_state(rv, RowState::Link(r.clone()));
        uppers
            .iter()
            .all(|(upper, handled)| self.fit(handled, r, upper).is_empty())
    }

    /// Makes the effects of `actual` part of `expected`, now and as `actual` grows, and returns
    /// what `expected` can't hold (effects.inference and effects.function-values). A raise that
    /// `handled` catches, as a `try … catch` does, must have its type, and doesn't reach
    /// `expected`, and neither does an effect that a `with` handles, whose arguments must be the
    /// handler's (handlers.with).
    pub fn fit(&mut self, handled: &Handled, actual: &Row, expected: &Row) -> Vec<Problem> {
        let mut a = self.row_contents(actual);
        let mut problems = Vec::new();
        match handled {
            Handled::Raise(h) => {
                if let Some(u) = a.raise.take()
                    && !self.unify(&u, h)
                {
                    problems.push(Problem::RaiseMismatch(*u, h.clone()));
                }
            }
            Handled::Effect(e, args) => {
                if let Some(given) = a.effect(e).map(<[Ty]>::to_vec) {
                    a = a.without_effect(e);
                    if !self.unify_all(&given, args) {
                        problems.push(Problem::EffectMismatch(e.clone(), given, args.clone()));
                    }
                }
            }
            Handled::Nothing => {}
        }
        match (self.open_var(actual), self.open_var(expected)) {
            (Some(ra), Some(re)) if ra == re => {}
            (Some(ra), _) => self.add_upper(ra, (expected.clone(), handled.clone())),
            (None, _) => {}
        }
        problems.extend(self.add(&a, expected));
        problems
    }

    /// Adds the effects `a`, whose tail is closed or holds row parameters, to a row: an open row
    /// grows to hold them, and any other row must hold them already.
    fn add(&mut self, a: &Row, expected: &Row) -> Vec<Problem> {
        let mut a = a.clone();
        // effects.error-type-raises: a raise of the error type fits every row.
        if a.raise
            .as_ref()
            .is_some_and(|t| *self.resolve(t) == Ty::Error)
        {
            a.raise = None;
        }
        let e = self.row_contents(expected);
        let mut problems = Vec::new();
        match (&a.raise, &e.raise) {
            (Some(u), Some(t)) => {
                if !self.unify(u, t) {
                    problems.push(Problem::RaiseMismatch((**u).clone(), (**t).clone()));
                }
            }
            (Some(u), None) if self.open_var(expected).is_none() => {
                problems.push(Problem::MissingRaise((**u).clone()));
            }
            (Some(_), None) | (None, _) => {}
        }
        // handlers.effects-in-rows: an effect the row holds takes its arguments, and an open row
        // holds the others.
        let open = self.open_var(expected).is_some();
        for (eff, args) in std::mem::take(&mut a.effects) {
            match e.effect(&eff).map(<[Ty]>::to_vec) {
                Some(held) if self.unify_all(&args, &held) => {}
                Some(held) => problems.push(Problem::EffectMismatch(eff, args, held)),
                None if open => a.effects.push((eff, args)),
                None => problems.push(Problem::MissingEffect(eff)),
            }
        }
        if let Some(rv) = self.open_var(expected) {
            problems.extend(self.grow(rv, &a, e.raise.as_deref()));
            return problems;
        }
        if a.io && !e.io {
            problems.push(Problem::MissingIo);
        }
        problems.extend(missing_params(&a.tail, &e.tail).map(|p| Problem::MissingVar(p.clone())));
        problems
    }

    /// Grows the open row `rv` by the effects `a` it lacks, and passes what it gains on to its
    /// upper bounds. `declared` is the raise the whole row already has.
    fn grow(&mut self, rv: RowVarId, a: &Row, declared: Option<&Ty>) -> Vec<Problem> {
        let RowState::Open(lower) = self.row_state(rv).clone() else {
            unreachable!("only an open row grows")
        };
        let mut problems = Vec::new();
        let raise = match (declared, &a.raise) {
            (None, Some(u)) if self.row_occurs(rv, u) => {
                problems.push(Problem::CyclicRaise((**u).clone()));
                None
            }
            (None, Some(u)) => Some(u.clone()),
            (Some(_) | None, _) => None,
        };
        let new: Vec<RowParam> = a
            .tail
            .params()
            .iter()
            .filter(|p| !lower.tail.params().contains(p))
            .cloned()
            .collect();
        let tail = (!new.is_empty()).then(|| {
            let mut all = lower.tail.params().to_vec();
            all.extend(new.iter().cloned());
            (Tail::of_params(new), Tail::of_params(all))
        });
        let effects = beyond(a, &lower).effects;
        let gained = Row {
            io: a.io && !lower.io,
            raise: raise.clone(),
            effects: effects.clone(),
            tail: tail.clone().map_or(Tail::Closed, |(new, _)| new),
        };
        let mut all_effects = lower.effects.clone();
        all_effects.extend(effects);
        let grown = Row {
            io: lower.io || gained.io,
            raise: raise.clone().or_else(|| lower.raise.clone()),
            effects: all_effects,
            tail: tail
                .clone()
                .map_or_else(|| lower.tail.clone(), |(_, all)| all),
        };
        self.set_row_state(rv, RowState::Open(grown.clone()));
        let mut upper_problems = Vec::new();
        if gained.io || raise.is_some() || tail.is_some() || !gained.effects.is_empty() {
            for (upper, handled) in self.uppers(rv) {
                upper_problems.extend(self.fit(&handled, &gained, &upper));
            }
        }
        // A raise that an upper bound rejects is reported where it comes, and the row doesn't
        // keep it, so later code isn't checked against it.
        if upper_problems
            .iter()
            .any(|p| matches!(p, Problem::RaiseMismatch(..)))
        {
            let kept = Row {
                raise: lower.raise,
                ..grown
            };
            self.set_row_state(rv, RowState::Open(kept));
        }
        problems.extend(upper_problems);
        problems
    }
}

/// The written row variables of the tail `inner` that the tail `outer` doesn't hold. An open
/// row's tail holds none, since it grows to hold them.
fn missing_params<'a>(inner: &'a Tail, outer: &'a Tail) -> impl Iterator<Item = &'a RowParam> {
    inner
        .params()
        .iter()
        .filter(move |p| !p.is_passed() && !outer.params().contains(p))
}

/// The row `r` without the labels that the row `m` writes itself: what the open variable that
/// ends `m` stands for once `m` and `r` are one. So `{raise<E>, e}` and `{raise<Box>, r}` make
/// `e` the row `r`, not `{raise<Box>, r}`.
fn beyond(r: &Row, m: &Row) -> Row {
    Row {
        io: r.io && !m.io,
        raise: if m.raise.is_some() {
            None
        } else {
            r.raise.clone()
        },
        effects: r
            .effects
            .iter()
            .filter(|(e, _)| m.effect(e).is_none())
            .cloned()
            .collect(),
        tail: r.tail.clone(),
    }
}
