//! The unification variables of one body, and the open rows.

use stilt_syntax::TextRange;

use super::{FnTy, Handled, Row, RowVarId, Tail, Ty, VarId, apply};

/// What an unsolved type variable may become.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// Any type.
    Any,
    /// The type of an integer literal: any numeric type (numbers.integer-literals).
    IntLiteral,
    /// The type of a float literal: a float type (numbers.float-literals).
    FloatLiteral,
}

/// An unsolved variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VarInfo {
    /// The variable.
    pub id: VarId,
    /// What it may become.
    pub kind: Kind,
    /// Where it was made.
    pub origin: TextRange,
    /// Whether the variable has met the error type, so that what it stands for may be unknown
    /// because of another error (errors.error-type).
    pub tainted: bool,
}

#[derive(Clone, Debug)]
struct Var {
    kind: Kind,
    origin: TextRange,
    solution: Option<Ty>,
    /// Where the code that gave it its solution is, when the table knew (goal
    /// one-form-per-reader).
    solved_at: Option<TextRange>,
    tainted: bool,
}

/// What an open row is so far.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RowState {
    /// The effects added so far, whose tail is closed or holds row parameters.
    Open(Row),
    /// The open row is this row, to which its upper bounds have moved.
    Link(Row),
}

#[derive(Clone, Debug)]
struct RowVar {
    state: RowState,
    /// The rows it must fit in, each with the raise type that it handles on the way, as a
    /// `try … catch` does.
    uppers: Vec<(Row, Handled)>,
    /// Whether it stands for the union of the rows of some function values, such as the elements of
    /// a list literal, or for the effects of a closure's body (effects.function-value-unions). Only
    /// those can add effects to it: unifying it with another row never does.
    least: bool,
}

/// The variables and open rows of one body.
#[derive(Clone, Debug, Default)]
pub struct Table {
    vars: Vec<Var>,
    rows: Vec<RowVar>,
    /// Where the code that the unification under way checks is, which each variable it solves
    /// records.
    site: Option<TextRange>,
}

fn index(i: u32) -> usize {
    i as usize
}

impl Table {
    /// A new type variable, created by the code at `origin`.
    ///
    /// # Panics
    ///
    /// If a body has more than 4G of them.
    pub fn fresh(&mut self, kind: Kind, origin: TextRange) -> Ty {
        let id = VarId(u32::try_from(self.vars.len()).expect("under 4G variables"));
        self.vars.push(Var {
            kind,
            origin,
            solution: None,
            solved_at: None,
            tainted: false,
        });
        Ty::Var(id)
    }

    /// The number of type variables made so far.
    #[must_use]
    pub fn var_count(&self) -> usize {
        self.vars.len()
    }

    /// The type variable made `i`-th.
    ///
    /// # Panics
    ///
    /// If a body has more than 4G of them.
    #[must_use]
    pub fn var(&self, i: usize) -> Ty {
        Ty::Var(VarId(u32::try_from(i).expect("under 4G variables")))
    }

    /// A row that is only an open row with nothing in it yet.
    ///
    /// # Panics
    ///
    /// If a body has more than 4G of them.
    pub fn fresh_row(&mut self, least: bool) -> Row {
        let id = RowVarId(u32::try_from(self.rows.len()).expect("under 4G rows"));
        self.rows.push(RowVar {
            state: RowState::Open(Row::EMPTY),
            uppers: Vec::new(),
            least,
        });
        Row {
            tail: Tail::Var(id),
            ..Row::EMPTY
        }
    }

    /// The type with its outermost solved variables replaced by their solutions. A variable
    /// the table doesn't have is one of a frozen type, whose body is done, so it is unsolved.
    #[must_use]
    pub fn resolve<'a>(&'a self, t: &'a Ty) -> &'a Ty {
        match t {
            Ty::Var(v) => match self.vars.get(index(v.0)).and_then(|v| v.solution.as_ref()) {
                Some(solution) => self.resolve(solution),
                None => t,
            },
            _ => t,
        }
    }

    /// Where the variable `t` itself was made, whatever variable it was later made one with.
    #[must_use]
    pub fn origin(&self, t: &Ty) -> Option<TextRange> {
        match t {
            Ty::Var(v) => self.vars.get(index(v.0)).map(|v| v.origin),
            _ => None,
        }
    }

    /// The unsolved variable that the type is, if it is one.
    #[must_use]
    pub fn unsolved(&self, t: &Ty) -> Option<VarInfo> {
        match self.resolve(t) {
            Ty::Var(id) => {
                let v = self.vars.get(index(id.0))?;
                Some(VarInfo {
                    id: *id,
                    kind: v.kind,
                    origin: v.origin,
                    tainted: v.tainted,
                })
            }
            _ => None,
        }
    }

    /// Solves the unsolved variable `v` with `t`. The variables of `t` are tainted if `v` was.
    ///
    /// # Panics
    ///
    /// If `v` isn't an unsolved variable.
    pub fn solve(&mut self, v: &Ty, t: Ty) {
        let info = self
            .unsolved(v)
            .expect("only an unsolved variable is solved");
        let tainted = info.tainted;
        if tainted {
            self.taint(&t);
        }
        let var = &mut self.vars[index(info.id.0)];
        var.solution = Some(t);
        var.solved_at = self.site;
    }

    /// Runs `f` with `at` as the site of the variables it solves, and gives what it gives.
    pub fn at<T>(&mut self, at: TextRange, f: impl FnOnce(&mut Self) -> T) -> T {
        let outer = self.enter(at);
        let out = f(self);
        self.leave(outer);
        out
    }

    /// Makes `at` the site of the variables solved until [`Table::leave`], and gives the site it
    /// replaces, which `leave` takes back.
    pub fn enter(&mut self, at: TextRange) -> Option<TextRange> {
        self.site.replace(at)
    }

    /// Gives back the site that [`Table::enter`] replaced.
    pub fn leave(&mut self, outer: Option<TextRange>) {
        self.site = outer;
    }

    /// How `t` came to be what it resolves to: for each variable on the way, where it was solved
    /// and with what, when the table knows where, and last, if it ends at an unsolved variable,
    /// where that one was made, as the literal whose type it is was.
    #[must_use]
    pub fn provenance(&self, t: &Ty) -> Vec<(TextRange, Ty)> {
        let mut steps = Vec::new();
        let mut at = t;
        while let Ty::Var(v) = at {
            let Some(var) = self.vars.get(index(v.0)) else {
                break;
            };
            let Some(solution) = var.solution.as_ref() else {
                steps.push((var.origin, at.clone()));
                break;
            };
            if let Some(solved) = var.solved_at {
                steps.push((solved, solution.clone()));
            }
            at = solution;
        }
        steps
    }

    /// Taints every unsolved variable in the type, as meeting the error type does.
    pub fn taint(&mut self, t: &Ty) {
        match self.resolve(t).clone() {
            Ty::Var(id) => self.vars[index(id.0)].tainted = true,
            Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().for_each(|t| self.taint(t)),
            Ty::App(head, ts) => {
                self.taint(&head);
                for t in &ts {
                    self.taint(t);
                }
            }
            Ty::Fn(f) => {
                f.params.iter().for_each(|(_, t)| self.taint(t));
                self.taint(&f.ret);
                if let Some(raise) = self.row_contents(&f.row).raise {
                    self.taint(&raise);
                }
            }
            Ty::Spread(s) => {
                self.taint(&s.pack);
                self.taint(&s.elem);
            }
            Ty::Handler(h) => {
                h.args.iter().chain(&h.answer).for_each(|t| self.taint(t));
                for (_, args) in self.row_contents(&h.row).effects {
                    for t in &args {
                        self.taint(t);
                    }
                }
            }
            Ty::Param(_) | Ty::SelfTy | Ty::Value(_) | Ty::Error => {}
        }
    }

    /// Whether the unsolved variable `v` occurs in `t`.
    #[must_use]
    pub fn occurs(&self, v: VarId, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Var(w) => *w == v,
            Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().any(|t| self.occurs(v, t)),
            Ty::App(head, ts) => self.occurs(v, head) || ts.iter().any(|t| self.occurs(v, t)),
            Ty::Fn(f) => {
                f.params.iter().any(|(_, t)| self.occurs(v, t))
                    || self.occurs(v, &f.ret)
                    || self
                        .row_contents(&f.row)
                        .raise
                        .is_some_and(|r| self.occurs(v, &r))
            }
            Ty::Spread(s) => self.occurs(v, &s.pack) || self.occurs(v, &s.elem),
            Ty::Handler(h) => h.args.iter().chain(&h.answer).any(|t| self.occurs(v, t)),
            Ty::Param(_) | Ty::SelfTy | Ty::Value(_) | Ty::Error => false,
        }
    }

    /// Whether the error type occurs in the type.
    #[must_use]
    pub fn mentions_error(&self, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Error => true,
            Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().any(|t| self.mentions_error(t)),
            Ty::App(head, ts) => {
                self.mentions_error(head) || ts.iter().any(|t| self.mentions_error(t))
            }
            Ty::Fn(f) => {
                f.params.iter().any(|(_, t)| self.mentions_error(t))
                    || self.mentions_error(&f.ret)
                    || self
                        .row_contents(&f.row)
                        .raise
                        .is_some_and(|r| self.mentions_error(&r))
            }
            Ty::Spread(s) => self.mentions_error(&s.pack) || self.mentions_error(&s.elem),
            Ty::Handler(h) => h
                .args
                .iter()
                .chain(&h.answer)
                .any(|t| self.mentions_error(t)),
            Ty::Param(_) | Ty::SelfTy | Ty::Var(_) | Ty::Value(_) => false,
        }
    }

    /// The type with every solved variable replaced, at every depth, and every row replaced by
    /// what it holds: the form of types after inference, which the later phases read.
    #[must_use]
    pub fn freeze(&self, t: &Ty) -> Ty {
        match self.resolve(t) {
            Ty::Con(item, args) => {
                Ty::Con(item.clone(), args.iter().map(|a| self.freeze(a)).collect())
            }
            Ty::Tuple(ts) => {
                Ty::Tuple(self.expand(ts, &mut |t, p| t.freeze(p), &mut |t, x, _| t.freeze(x)))
            }
            Ty::Spread(s) => Ty::spread(self.freeze(&s.pack), s.of.clone(), self.freeze(&s.elem)),
            Ty::App(head, ts) => apply(
                self.freeze(head),
                ts.iter().map(|t| self.freeze(t)).collect(),
            ),
            Ty::Fn(f) => Ty::Fn(Box::new(FnTy {
                generics: f.generics.clone(),
                bound_args: f.bound_args_with(|a| self.freeze(a)),
                params: self.expand_params(&f.params, &mut |t, p| t.freeze(p), &mut |t, x, _| {
                    t.freeze(x)
                }),
                ret: self.freeze(&f.ret),
                row: self.freeze_row(&f.row),
            })),
            Ty::Handler(h) => Ty::Handler(Box::new(super::HandlerTy {
                effect: h.effect.clone(),
                args: h.args.iter().map(|t| self.freeze(t)).collect(),
                answer: h.answer.as_ref().map(|t| self.freeze(t)),
                row: self.freeze_row(&h.row),
            })),
            t @ (Ty::Param(_) | Ty::SelfTy | Ty::Var(_) | Ty::Value(_) | Ty::Error) => t.clone(),
        }
    }

    /// The effects a row holds after inference, with its raise type frozen. Its tail is closed
    /// or holds row parameters.
    #[must_use]
    pub fn freeze_row(&self, r: &Row) -> Row {
        let mut r = self.row_contents(r);
        r.raise = r.raise.map(|t| Box::new(self.freeze(&t)));
        for (_, args) in &mut r.effects {
            *args = args.iter().map(|t| self.freeze(t)).collect();
        }
        r
    }

    // Rows

    /// What the open row `rv` holds so far.
    #[must_use]
    pub fn row_state(&self, rv: RowVarId) -> &RowState {
        &self.rows[index(rv.0)].state
    }

    /// Sets what the open row `rv` holds.
    pub fn set_row_state(&mut self, rv: RowVarId, state: RowState) {
        self.rows[index(rv.0)].state = state;
    }

    /// Whether `rv` stands for a union of rows, which only those rows add effects to.
    #[must_use]
    pub fn least(&self, rv: RowVarId) -> bool {
        self.rows[index(rv.0)].least
    }

    /// The rows an open row must fit in, each with the raise type that it handles on the way.
    #[must_use]
    pub fn uppers(&self, rv: RowVarId) -> Vec<(Row, Handled)> {
        self.rows[index(rv.0)].uppers.clone()
    }

    /// Adds a row that `rv` must fit in, with what it handles on the way.
    pub fn add_upper(&mut self, rv: RowVarId, bound: (Row, Handled)) {
        self.rows[index(rv.0)].uppers.push(bound);
    }

    /// The effects the row holds now: links followed, and each open row replaced by the
    /// effects added to it so far. Its tail is closed or holds row parameters. An open row may
    /// hold more later, which reach its upper bounds.
    #[must_use]
    pub fn row_contents(&self, r: &Row) -> Row {
        match &r.tail {
            Tail::Closed | Tail::Params(_) => r.clone(),
            Tail::Var(rv) => {
                let (RowState::Link(inner) | RowState::Open(inner)) = self.row_state(*rv);
                self.row_contents(inner).merge_labels(r)
            }
        }
    }

    /// Whether the row ends in an open row, which may still grow.
    #[must_use]
    pub fn is_open(&self, r: &Row) -> bool {
        match &r.tail {
            Tail::Closed | Tail::Params(_) => false,
            Tail::Var(rv) => match self.row_state(*rv) {
                RowState::Open(_) => true,
                RowState::Link(linked) => self.is_open(linked),
            },
        }
    }

    /// The open row variable that ends a row, if it ends in one.
    #[must_use]
    pub fn open_var(&self, r: &Row) -> Option<RowVarId> {
        match &r.tail {
            Tail::Var(rv) => match self.row_state(*rv) {
                RowState::Open(_) => Some(*rv),
                RowState::Link(linked) => self.open_var(linked),
            },
            Tail::Closed | Tail::Params(_) => None,
        }
    }

    /// Whether the open row `rv` occurs in `t`, through the rows of its function types.
    #[must_use]
    pub fn row_occurs(&self, rv: RowVarId, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Con(_, ts) | Ty::Tuple(ts) | Ty::App(_, ts) => {
                ts.iter().any(|t| self.row_occurs(rv, t))
            }
            Ty::Spread(s) => self.row_occurs(rv, &s.elem),
            Ty::Fn(f) => {
                f.params.iter().any(|(_, t)| self.row_occurs(rv, t))
                    || self.row_occurs(rv, &f.ret)
                    || self.row_mentions(rv, &f.row)
            }
            Ty::Handler(h) => {
                h.args
                    .iter()
                    .chain(&h.answer)
                    .any(|t| self.row_occurs(rv, t))
                    || self.row_mentions(rv, &h.row)
            }
            Ty::Param(_) | Ty::SelfTy | Ty::Var(_) | Ty::Value(_) | Ty::Error => false,
        }
    }

    /// Whether the open row `rv` occurs in `r`: as its tail, or in its raise type.
    #[must_use]
    pub fn row_mentions(&self, rv: RowVarId, r: &Row) -> bool {
        r.raise.as_ref().is_some_and(|t| self.row_occurs(rv, t))
            || r.effects
                .iter()
                .any(|(_, args)| args.iter().any(|t| self.row_occurs(rv, t)))
            || match &r.tail {
                Tail::Var(v) if *v == rv => true,
                Tail::Var(v) => {
                    let (RowState::Link(inner) | RowState::Open(inner)) = self.row_state(*v);
                    self.row_mentions(rv, inner)
                }
                Tail::Closed | Tail::Params(_) => false,
            }
    }

    /// The type with its outermost solved variables replaced, and a constructor applied through a
    /// variable that stands for one made that constructor applied (traits.constructor-parameters).
    #[must_use]
    pub fn shape(&self, t: &Ty) -> Ty {
        match self.resolve(t) {
            Ty::App(head, args) => match self.resolve(head) {
                Ty::Var(_) | Ty::Param(_) | Ty::SelfTy => Ty::App(head.clone(), args.clone()),
                solved => apply(solved.clone(), args.clone()),
            },
            t => t.clone(),
        }
    }

    /// The name of a numeric type, such as `u8`, if the type is one.
    #[must_use]
    pub fn numeric_name(&self, t: &Ty) -> Option<String> {
        self.resolve(t).numeric_name().map(str::to_owned)
    }

    /// The name of an integer type, if the type is one.
    #[must_use]
    pub fn integer_name(&self, t: &Ty) -> Option<String> {
        self.resolve(t).integer_name().map(str::to_owned)
    }

    /// Whether the type is `Never`.
    #[must_use]
    pub fn is_never(&self, t: &Ty) -> bool {
        *self.resolve(t) == Ty::never()
    }
}
