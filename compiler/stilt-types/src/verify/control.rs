//! The forms whose paths meet (facts.joins, facts.paths-that-leave and facts.match-arms): `if`, `if
//! let`, `match` and `let … else`, a value's `else`, `try … catch` and `with`.

use super::dbm::{Term, ZERO};
use super::state::State;
use super::values::Value;
use super::walker::Walker;
use crate::tast::{Arm, Block, Catch, Expr, ExprKind, Pat, PatKind, StmtKind};
use crate::ty::Ty;

impl Walker<'_> {
    /// `if c { … } else …`: each branch from the facts where `c` is true or false.
    pub(crate) fn if_else(
        &mut self,
        st: &mut State,
        c: &Expr,
        then: &Block,
        otherwise: Option<&Expr>,
        ty: &Ty,
    ) -> Option<Value> {
        let ends = self.if_paths(st, c, then, otherwise);
        *st = self.join(ends);
        self.opaque(st, ty)
    }

    /// The states at the ends of an `if`'s branches, before they meet.
    pub(crate) fn if_paths(
        &mut self,
        st: &mut State,
        c: &Expr,
        then: &Block,
        otherwise: Option<&Expr>,
    ) -> Vec<State> {
        let (mut t, mut f) = self.cond(st, c);
        let mut ends = self.block_paths(&mut t, then);
        match otherwise {
            Some(e) => ends.extend(self.expr_paths(&mut f, e)),
            None => ends.push(f),
        }
        ends
    }

    /// `if let P = e { … } else …`, a `match` arm without a guard (expressions.if-let).
    pub(crate) fn if_let(
        &mut self,
        st: &mut State,
        (p, e): (&Pat, &Expr),
        then: &Block,
        otherwise: Option<&Expr>,
        ty: &Ty,
    ) -> Option<Value> {
        let ends = self.if_let_paths(st, p, e, then, otherwise);
        *st = self.join(ends);
        self.opaque(st, ty)
    }

    fn if_let_paths(
        &mut self,
        st: &mut State,
        p: &Pat,
        e: &Expr,
        then: &Block,
        otherwise: Option<&Expr>,
    ) -> Vec<State> {
        let value = self.eval(st, e);
        let held: Vec<Term> = value.iter().map(|v| v.term).collect();
        self.holding(&held, |w| {
            let before = st.bindings();
            let mut fails = st.clone();
            Self::fails(&mut fails, p, value, false);
            let mut t = st.clone();
            w.match_pattern(&mut t, p, value);
            let mut ends = w.block_paths(&mut t, then);
            for s in &mut ends {
                s.scope_to(&before);
            }
            match otherwise {
                Some(e) => ends.extend(w.expr_paths(&mut fails, e)),
                None => ends.push(fails),
            }
            ends
        })
    }

    /// `match e { … }`.
    pub(crate) fn matches(
        &mut self,
        st: &mut State,
        scrutinee: &Expr,
        arms: &[Arm],
        ty: &Ty,
    ) -> Option<Value> {
        let ends = self.match_paths(st, scrutinee, arms);
        *st = self.join(ends);
        self.opaque(st, ty)
    }

    /// The states at the ends of a `match`'s arms: each later arm starts with the facts the
    /// earlier arms leave where they fail (facts.match-arms).
    pub(crate) fn match_paths(
        &mut self,
        st: &mut State,
        scrutinee: &Expr,
        arms: &[Arm],
    ) -> Vec<State> {
        let value = self.eval(st, scrutinee);
        let held: Vec<Term> = value.iter().map(|v| v.term).collect();
        self.holding(&held, |w| w.arms(st, value, arms))
    }

    /// The arms of a `match` or a `catch`, on a scrutinee whose value is `value`.
    pub(crate) fn arms(&mut self, st: &State, value: Option<Value>, arms: &[Arm]) -> Vec<State> {
        let before = st.bindings();
        let mut next = st.clone();
        let mut ends = Vec::new();
        for arm in arms {
            let mut matched = next.clone();
            self.match_pattern(&mut matched, &arm.pattern, value);
            let (mut body, failed) = match &arm.guard {
                None => (matched, None),
                Some(g) if or_pattern(&arm.pattern) => {
                    let (t, f) = self.guard_loop(&mut matched, g, &arm.pattern);
                    (t, Some(f))
                }
                Some(g) => {
                    let (t, f) = self.cond(&mut matched, g);
                    (t, Some(f))
                }
            };
            for s in self.expr_paths(&mut body, &arm.body) {
                let mut s = s;
                s.scope_to(&before);
                ends.push(s);
            }
            let mut fails = next.clone();
            Self::fails(&mut fails, &arm.pattern, value, arm.guard.is_some());
            next = match failed {
                Some(mut f) => {
                    f.scope_to(&before);
                    self.join(vec![fails, f])
                }
                None => fails,
            };
        }
        ends
    }

    /// The facts where a pattern, matched against `value`, doesn't match: a later arm knows `t + 0`
    /// non-zero when an arm before it, with no guard, is the literal 0 alone (facts.match-arms).
    fn fails(st: &mut State, p: &Pat, value: Option<Value>, guarded: bool) {
        if guarded {
            return;
        }
        if let (PatKind::Int(text), Some(v)) = (&p.kind, value)
            && super::scan::literal(text) == Some(0)
            && v.linear
            && v.d == 0
        {
            st.facts.mark_nonzero(v.term);
        }
    }

    /// A pattern matched against `value`: its bindings take new terms with their bounds only,
    /// and, for a scrutinee of a linear form `t + d`, a literal `c` adds `t = c − d`, and an
    /// or-pattern of literals the join of each one's (facts.bindings-and-assignments and
    /// facts.match-arms).
    pub(crate) fn match_pattern(&mut self, st: &mut State, p: &Pat, value: Option<Value>) {
        self.bind_pattern(st, p);
        let Some((t, d)) = value.and_then(|v| v.form()) else {
            return;
        };
        match &p.kind {
            PatKind::Int(text) => {
                if let Some(c) = super::scan::literal(text) {
                    st.facts.assume(t, ZERO, c - d);
                    st.facts.assume(ZERO, t, d - c);
                }
            }
            PatKind::Or(ps) if ps.iter().all(|p| matches!(p.kind, PatKind::Int(_))) => {
                let each: Vec<State> = ps
                    .iter()
                    .map(|p| {
                        let mut s = st.clone();
                        self.match_pattern(&mut s, p, value);
                        s
                    })
                    .collect();
                *st = self.join(each);
            }
            _ => {}
        }
    }

    /// `a else b`: `b` runs where `a` gives no value, and the paths meet.
    pub(crate) fn else_(&mut self, st: &mut State, a: &Expr, b: &Expr, ty: &Ty) -> Option<Value> {
        self.eval(st, a);
        let mut otherwise = st.clone();
        self.eval(&mut otherwise, b);
        *st = self.join(vec![st.clone(), otherwise]);
        self.opaque(st, ty)
    }

    /// `try e` and `try e catch { … }`: each call in `e` that raises the error the arms handle
    /// is a path to them (facts.paths-that-leave).
    pub(crate) fn try_(
        &mut self,
        st: &mut State,
        e: &Expr,
        catch: Option<&Catch>,
        ty: &Ty,
    ) -> Option<Value> {
        let Some(catch) = catch.filter(|c| !c.handles_never()) else {
            return self.eval(st, e);
        };
        self.paths
            .catches
            .push((catch.error.clone(), self.quiet, Vec::new()));
        self.eval(st, e);
        let (_, _, raised) = self
            .paths
            .catches
            .pop()
            .unwrap_or((Ty::Error, 0, Vec::new()));
        let mut ends = vec![st.clone()];
        if !raised.is_empty() {
            let from = self.join(raised);
            ends.extend(self.arms(&from, None, &catch.arms));
        }
        *st = self.join(ends);
        self.opaque(st, ty)
    }

    /// `with h { … }`: when the handler takes control, each performance and each call whose row
    /// holds an effect or a row variable is a path to the `with`'s end (facts.paths-that-leave).
    pub(crate) fn with(&mut self, st: &mut State, h: &Expr, b: &Block, ty: &Ty) -> Option<Value> {
        self.eval(st, h);
        let before = st.bindings();
        let control = matches!(&h.ty, Ty::Handler(t) if t.answer.is_some());
        self.paths.withs.push((self.quiet, control.then(Vec::new)));
        self.block(st, b);
        let ended = self
            .paths
            .withs
            .pop()
            .and_then(|(_, p)| p)
            .unwrap_or_default();
        let mut ends = vec![st.clone()];
        ends.extend(ended);
        for s in &mut ends {
            s.scope_to(&before);
        }
        *st = self.join(ends);
        self.opaque(st, ty)
    }

    /// The states at the end of a block, apart where its last statement is an `if` or a
    /// `match`, as the paths back to a loop's head read them (facts.loop-heads); their join is the
    /// block's end.
    pub(crate) fn block_paths(&mut self, st: &mut State, b: &Block) -> Vec<State> {
        let Some((last, front)) = b.split_last() else {
            return vec![st.clone()];
        };
        let before = st.bindings();
        for s in front {
            self.stmt(st, s);
            self.end_stmt(st, None);
        }
        let mut ends = match &last.kind {
            StmtKind::Expr(e)
                if matches!(
                    e.kind,
                    ExprKind::If(..) | ExprKind::IfLet(..) | ExprKind::Match(..)
                ) =>
            {
                self.expr_paths(st, e)
            }
            _ => {
                self.stmt(st, last);
                vec![st.clone()]
            }
        };
        for s in &mut ends {
            self.end_stmt(s, None);
            s.scope_to(&before);
        }
        ends
    }

    /// The states at the end of an expression, apart for an `if` or a `match`.
    pub(crate) fn expr_paths(&mut self, st: &mut State, e: &Expr) -> Vec<State> {
        match &e.kind {
            ExprKind::If(c, then, otherwise) => self.if_paths(st, c, then, otherwise.as_deref()),
            ExprKind::IfLet(p, x, then, otherwise) => {
                self.if_let_paths(st, p, x, then, otherwise.as_deref())
            }
            ExprKind::Match(x, arms) => self.match_paths(st, x, arms),
            ExprKind::Block(b) => self.block_paths(st, b),
            _ => {
                self.eval(st, e);
                vec![st.clone()]
            }
        }
    }
}

/// Whether a pattern holds an or-pattern, whose guard may run once for each way it matches
/// (patterns.guards).
fn or_pattern(p: &Pat) -> bool {
    match &p.kind {
        PatKind::Or(_) => true,
        PatKind::Tuple(ps) | PatKind::Variant(_, ps) | PatKind::List(ps, _) => {
            ps.iter().any(or_pattern)
        }
        PatKind::Record(fields) => fields.iter().any(|(_, p)| or_pattern(p)),
        _ => false,
    }
}
