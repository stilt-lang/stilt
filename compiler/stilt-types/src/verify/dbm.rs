//! The facts at a point of a body (facts.difference-facts): difference facts `t − u ≤ c` between
//! its terms, kept closed, with exact constants, the terms known non-zero, and the keys present in
//! maps (facts.map-keys). A contradictory set marks a point that is never reached.

use std::collections::BTreeSet;

/// An integer value that the analysis follows, or a version of a binding (facts.terms and
/// facts.map-keys), by a number that each body's analysis gives once.
pub(crate) type Term = u32;

/// The term that stands for 0.
pub(crate) const ZERO: Term = 0;

/// No fact on a pair: no `c` bounds `t − u`.
pub(crate) const INF: i128 = i128::MAX;

/// `a + b`, none if either is none. No sum of the analysis's constants comes near the width of
/// `i128`, which is why they are exact (facts.difference-facts).
pub(crate) fn plus(a: i128, b: i128) -> i128 {
    if a == INF || b == INF {
        INF
    } else {
        a.saturating_add(b).min(INF - 1)
    }
}

/// A key of a map (facts.map-keys): an integer binding's value by its linear form, a binding of
/// another type at a version, or a literal by its text.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Key {
    Form(Term, i128),
    Version(Term),
    Text(String),
}

/// A set of facts: the terms it holds, in increasing order, the difference facts between them,
/// closed, the non-zero terms and the keys present at each version of a map.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Facts {
    terms: Vec<Term>,
    /// `m[i * n + j]` bounds `terms[i] − terms[j]`.
    m: Vec<i128>,
    nonzero: BTreeSet<Term>,
    pub(crate) present: BTreeSet<(Term, Key)>,
    bottom: bool,
    /// Whether the body's count passes 64, so that only bounds are kept (facts.large-bodies).
    capped: bool,
}

impl Facts {
    /// The facts of a body's start: zero alone.
    pub(crate) fn new(capped: bool) -> Self {
        Self::over(vec![ZERO], capped)
    }

    /// No facts on the terms `terms`, which are in increasing order, zero first.
    pub(crate) fn over(terms: Vec<Term>, capped: bool) -> Self {
        let n = terms.len();
        let mut m = vec![INF; n * n];
        for i in 0..n {
            m[i * n + i] = 0;
        }
        Self {
            terms,
            m,
            nonzero: BTreeSet::new(),
            present: BTreeSet::new(),
            bottom: false,
            capped,
        }
    }

    /// Whether the set is contradictory, so that its point is never reached.
    pub(crate) fn is_bottom(&self) -> bool {
        self.bottom
    }

    /// Marks the point as never reached: what follows a path that leaves.
    pub(crate) fn unreached(&mut self) {
        self.bottom = true;
    }

    pub(crate) fn terms(&self) -> &[Term] {
        &self.terms
    }

    fn n(&self) -> usize {
        self.terms.len()
    }

    fn at(&self, t: Term) -> Option<usize> {
        self.terms.binary_search(&t).ok()
    }

    pub(crate) fn has(&self, t: Term) -> bool {
        self.at(t).is_some()
    }

    /// Adds a term newer than every term the set holds, with no facts.
    pub(crate) fn add_term(&mut self, t: Term) {
        debug_assert!(self.terms.last().is_none_or(|last| *last < t));
        let n = self.n();
        let mut m = vec![INF; (n + 1) * (n + 1)];
        for i in 0..n {
            m[i * (n + 1)..i * (n + 1) + n].copy_from_slice(&self.m[i * n..i * n + n]);
        }
        m[n * (n + 1) + n] = 0;
        self.terms.push(t);
        self.m = m;
    }

    /// The least `c` such that `t − u ≤ c` holds, or [`INF`].
    pub(crate) fn get(&self, t: Term, u: Term) -> i128 {
        match (self.at(t), self.at(u)) {
            (Some(i), Some(j)) => self.m[i * self.n() + j],
            _ => INF,
        }
    }

    /// Whether the facts give `t − u ≤ c`; a point never reached gives every fact.
    pub(crate) fn gives(&self, t: Term, u: Term, c: i128) -> bool {
        self.bottom || (t == u && c >= 0) || self.get(t, u) <= c
    }

    /// The least and greatest values the facts allow `t`, none where nothing bounds it.
    pub(crate) fn bounds(&self, t: Term) -> (Option<i128>, Option<i128>) {
        let lo = self.get(ZERO, t);
        let hi = self.get(t, ZERO);
        ((lo != INF).then(|| -lo), (hi != INF).then_some(hi))
    }

    pub(crate) fn is_nonzero(&self, t: Term) -> bool {
        self.bottom || self.nonzero.contains(&t)
    }

    /// Adds the fact `t − u ≤ c` and closes the set again.
    pub(crate) fn assume(&mut self, t: Term, u: Term, c: i128) {
        if self.bottom {
            return;
        }
        if t == u {
            if c < 0 {
                self.bottom = true;
            }
            return;
        }
        if self.raw(t, u, c) {
            self.tighten();
            self.cap();
        }
    }

    /// Makes `t` non-zero, and closes the set again.
    pub(crate) fn mark_nonzero(&mut self, t: Term) {
        if self.has(t) && self.nonzero.insert(t) {
            self.tighten();
            self.cap();
        }
    }

    /// Adds `t − u ≤ c` to a closed set, closing it by the paths through the new fact, and
    /// returns whether anything changed.
    fn raw(&mut self, t: Term, u: Term, c: i128) -> bool {
        let (Some(row), Some(col)) = (self.at(t), self.at(u)) else {
            return false;
        };
        let n = self.n();
        if self.m[row * n + col] <= c {
            return false;
        }
        let into_a: Vec<i128> = (0..n).map(|from| self.m[from * n + row]).collect();
        let from_b: Vec<i128> = self.m[col * n..col * n + n].to_vec();
        for (from, &ia) in into_a.iter().enumerate() {
            if ia == INF {
                continue;
            }
            let through = plus(ia, c);
            for (to, &bj) in from_b.iter().enumerate() {
                let sum = plus(through, bj);
                if sum < self.m[from * n + to] {
                    self.m[from * n + to] = sum;
                }
            }
        }
        if (0..n).any(|from| self.m[from * n + from] < 0) {
            self.bottom = true;
        }
        true
    }

    /// Applies the non-zero terms: one bounded below by 0 is bounded below by 1, and one bounded
    /// above by 0 is bounded above by −1, until nothing changes (facts.difference-facts).
    fn tighten(&mut self) {
        loop {
            if self.bottom {
                return;
            }
            let mut changed = false;
            for t in self.nonzero.clone() {
                if self.get(ZERO, t) <= 0 {
                    changed |= self.raw(ZERO, t, -1);
                }
                if self.get(t, ZERO) <= 0 {
                    changed |= self.raw(t, ZERO, -1);
                }
            }
            if !changed {
                return;
            }
        }
    }

    /// Past the count of facts.large-bodies, drops every fact between two terms neither of which is
    /// zero, once the set is closed, so that each term keeps only its bounds.
    fn cap(&mut self) {
        if !self.capped {
            return;
        }
        let n = self.n();
        for i in 1..n {
            for j in 1..n {
                if i != j {
                    self.m[i * n + j] = INF;
                }
            }
        }
    }

    /// Closes a set that isn't closed, as a widened one isn't (facts.widening).
    pub(crate) fn close(&mut self) {
        let n = self.n();
        for k in 0..n {
            for i in 0..n {
                let ik = self.m[i * n + k];
                if ik == INF {
                    continue;
                }
                for j in 0..n {
                    let v = plus(ik, self.m[k * n + j]);
                    if v < self.m[i * n + j] {
                        self.m[i * n + j] = v;
                    }
                }
            }
        }
        if (0..n).any(|i| self.m[i * n + i] < 0) {
            self.bottom = true;
        }
        self.tighten();
        self.cap();
    }

    /// Keeps only the terms that `keep` names, and zero: every fact between them is already
    /// there, since the set is closed (facts.difference-facts).
    pub(crate) fn keep(&mut self, keep: &dyn Fn(Term) -> bool) {
        let kept: Vec<usize> = (0..self.n())
            .filter(|&i| i == 0 || keep(self.terms[i]))
            .collect();
        if kept.len() == self.n() {
            return;
        }
        let n = self.n();
        let k = kept.len();
        let mut m = vec![INF; k * k];
        for (a, &i) in kept.iter().enumerate() {
            for (b, &j) in kept.iter().enumerate() {
                m[a * k + b] = self.m[i * n + j];
            }
        }
        self.terms = kept.iter().map(|&i| self.terms[i]).collect();
        self.m = m;
        let terms = &self.terms;
        self.nonzero.retain(|t| terms.binary_search(t).is_ok());
    }

    /// The facts on the terms `target`, in increasing order, that every path keeps: for each
    /// pair, the greatest `c` among the paths', each path reading a term of `target` as the term
    /// that `own` gives it there; a term non-zero when it is on every path (facts.joins). No path
    /// is contradictory, and there is at least one.
    pub(crate) fn merge(target: Vec<Term>, paths: &[(&Facts, &dyn Fn(Term) -> Term)]) -> Facts {
        let capped = paths.iter().any(|(f, _)| f.capped);
        let mut out = Facts::over(target, capped);
        let n = out.n();
        let at: Vec<Vec<Option<usize>>> = paths
            .iter()
            .map(|(f, own)| out.terms.iter().map(|t| f.at(own(*t))).collect())
            .collect();
        for i in 0..n {
            for j in 0..n {
                if i == j {
                    continue;
                }
                let mut c = i128::MIN;
                for ((f, _), at) in paths.iter().zip(&at) {
                    let v = match (at[i], at[j]) {
                        (Some(a), Some(b)) => f.m[a * f.n() + b],
                        _ => INF,
                    };
                    c = c.max(v);
                }
                out.m[i * n + j] = c;
            }
        }
        out.nonzero = out
            .terms
            .iter()
            .copied()
            .filter(|t| paths.iter().all(|(f, own)| f.nonzero.contains(&own(*t))))
            .collect();
        out.close();
        out
    }

    /// facts.widening's widening of the last set at a loop's head by the join of a visit: pair by
    /// pair, the last `c` where the join's is no greater, and otherwise the least threshold at
    /// least as large as the join's, or no fact; the non-zero terms and present keys that both
    /// have. Both are on the same terms, and the result isn't closed.
    pub(crate) fn widen(&self, joined: &Facts, thresholds: &[i128]) -> Facts {
        let mut out = self.clone();
        for (o, &j) in out.m.iter_mut().zip(&joined.m) {
            if j > *o {
                *o = match thresholds.binary_search(&j) {
                    Ok(i) => thresholds[i],
                    Err(i) => thresholds.get(i).copied().unwrap_or(INF),
                };
            }
        }
        out.nonzero = self
            .nonzero
            .intersection(&joined.nonzero)
            .copied()
            .collect();
        out.present = self
            .present
            .intersection(&joined.present)
            .cloned()
            .collect();
        out
    }

    /// Whether two sets on the same terms hold the same facts, before closure, the same
    /// non-zero terms and the same present keys (facts.widening).
    pub(crate) fn same(&self, other: &Facts) -> bool {
        self.terms == other.terms
            && self.m == other.m
            && self.nonzero == other.nonzero
            && self.present == other.present
    }
}
