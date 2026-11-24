//! The facts that hold at a point of a function: relations between integers, the lengths of
//! lists, and the indices known to be in bounds of them. A set of facts only ever states what
//! every path to its point makes true, so a smaller set is always a safe one.

use crate::mir::Local;

/// An integer that a relation compares: a local's value, or a constant, as a signed 64-bit
/// integer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Term {
    Local(Local),
    Const(i64),
}

/// A word in memory that holds a list: the slot of a local that lives there, or a word that an
/// `inout` parameter points to, at an offset in words.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Place {
    Slot(Local),
    Param(Local, u32),
}

/// What holds a list: a local, or a place.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Holder {
    Local(Local),
    Place(Place),
}

/// A relation between two integers, signed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Rel {
    Lt(Term, Term),
    Le(Term, Term),
}

impl Rel {
    /// The relation that holds when this one doesn't.
    pub(crate) fn negated(self) -> Self {
        match self {
            Rel::Lt(a, b) => Rel::Le(b, a),
            Rel::Le(a, b) => Rel::Lt(b, a),
        }
    }

    fn map(self, f: &impl Fn(Local) -> Local) -> Self {
        match self {
            Rel::Lt(a, b) => Rel::Lt(map_term(a, f), map_term(b, f)),
            Rel::Le(a, b) => Rel::Le(map_term(a, f), map_term(b, f)),
        }
    }

    fn terms(self) -> [Term; 2] {
        match self {
            Rel::Lt(a, b) | Rel::Le(a, b) => [a, b],
        }
    }
}

fn map_term(t: Term, f: &impl Fn(Local) -> Local) -> Term {
    match t {
        Term::Local(l) => Term::Local(f(l)),
        Term::Const(_) => t,
    }
}

/// A fact about the values of locals at a point.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Fact {
    Rel(Rel),
    /// The local is 1 when the relation holds and 0 otherwise.
    Cond(Local, Rel),
    /// The local is the length of the list that the holder holds.
    Len(Local, Holder),
    /// The local holds the word that the place holds.
    Holds(Local, Place),
    /// The term is an index in bounds of the list that the holder holds.
    InBounds(Term, Holder),
}

impl Fact {
    /// The fact with each local that holds a value renamed by `f`. A place names the memory
    /// itself, which a renaming leaves alone.
    pub(crate) fn map(self, f: &impl Fn(Local) -> Local) -> Self {
        let holder = |h: Holder| match h {
            Holder::Local(l) => Holder::Local(f(l)),
            Holder::Place(_) => h,
        };
        match self {
            Fact::Rel(r) => Fact::Rel(r.map(f)),
            Fact::Cond(c, r) => Fact::Cond(f(c), r.map(f)),
            Fact::Len(n, h) => Fact::Len(f(n), holder(h)),
            Fact::Holds(l, p) => Fact::Holds(f(l), p),
            Fact::InBounds(i, h) => Fact::InBounds(map_term(i, f), holder(h)),
        }
    }

    /// Whether the fact depends on the value of the local `l`.
    pub(crate) fn mentions(self, l: Local) -> bool {
        let term = |t: Term| t == Term::Local(l);
        let rel = |r: Rel| r.terms().into_iter().any(term);
        let holder = |h: Holder| h == Holder::Local(l);
        match self {
            Fact::Rel(r) => rel(r),
            Fact::Cond(c, r) => c == l || rel(r),
            Fact::Len(n, h) => n == l || holder(h),
            Fact::Holds(m, _) => m == l,
            Fact::InBounds(i, h) => term(i) || holder(h),
        }
    }

    /// The place whose contents the fact depends on, if any.
    fn place(self) -> Option<Place> {
        match self {
            Fact::Len(_, Holder::Place(p))
            | Fact::InBounds(_, Holder::Place(p))
            | Fact::Holds(_, p) => Some(p),
            _ => None,
        }
    }
}

/// Facts beyond this many are dropped, the largest first, which keeps the analysis linear in a
/// function's size and only ever forgets.
const LIMIT: usize = 512;

/// A query looks through at most this many terms known equal to each it compares, which
/// bounds its work.
const EQUALS: usize = 4;

/// The least and the greatest term, local and holder, which bound the facts that begin alike.
const LOW: Term = Term::Local(Local(0));
const HIGH: Term = Term::Const(i64::MAX);
const FIRST: Local = Local(0);
const LAST: Local = Local(u32::MAX);
const LOW_HOLDER: Holder = Holder::Local(FIRST);
const HIGH_HOLDER: Holder = Holder::Place(HIGH_PLACE);
const LOW_PLACE: Place = Place::Slot(FIRST);
const HIGH_PLACE: Place = Place::Param(LAST, u32::MAX);

/// A set of facts that hold together, in their order, each once: the facts that begin alike,
/// such as the relations of one term to others, lie together, so a query reads only those.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Facts(Vec<Fact>);

impl Facts {
    pub(crate) fn insert(&mut self, f: Fact) {
        if let Err(at) = self.0.binary_search(&f) {
            self.0.insert(at, f);
        }
    }

    pub(crate) fn contains(&self, f: Fact) -> bool {
        self.0.binary_search(&f).is_ok()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = Fact> + '_ {
        self.0.iter().copied()
    }

    /// The facts from `low` to `high`, both included, in their order.
    fn between(&self, low: Fact, high: Fact) -> &[Fact] {
        let start = self.0.partition_point(|f| *f < low);
        let len = self.0[start..].partition_point(|f| *f <= high);
        &self.0[start..start + len]
    }

    /// The facts `a < x`, if `strict`, or `a <= x`, whatever the term `x`: the relations that
    /// state what `a` is below.
    fn above(&self, a: Term, strict: bool) -> &[Fact] {
        let rel = |x| if strict { Rel::Lt(a, x) } else { Rel::Le(a, x) };
        self.between(Fact::Rel(rel(LOW)), Fact::Rel(rel(HIGH)))
    }

    /// The facts that `i` is an index in bounds of some list.
    fn bounds_of(&self, i: Term) -> &[Fact] {
        self.between(
            Fact::InBounds(i, LOW_HOLDER),
            Fact::InBounds(i, HIGH_HOLDER),
        )
    }

    /// The facts of the places whose word the local `l` holds.
    fn held_by(&self, l: Local) -> &[Fact] {
        self.between(Fact::Holds(l, LOW_PLACE), Fact::Holds(l, HIGH_PLACE))
    }

    /// The facts of which place each local holds the word of.
    fn holding(&self) -> &[Fact] {
        self.between(Fact::Holds(FIRST, LOW_PLACE), Fact::Holds(LAST, HIGH_PLACE))
    }

    /// The facts of the lengths of lists.
    fn lengths(&self) -> &[Fact] {
        self.between(Fact::Len(FIRST, LOW_HOLDER), Fact::Len(LAST, HIGH_HOLDER))
    }

    /// Keeps the facts that also hold in `other`, and returns whether any was dropped.
    pub(crate) fn meet(&mut self, other: &Self) -> bool {
        let before = self.0.len();
        let mut rest = other.0.iter().peekable();
        self.0.retain(|f| {
            while rest.next_if(|g| *g < f).is_some() {}
            rest.next_if_eq(&f).is_some()
        });
        self.0.len() != before
    }

    /// Keeps at most [`LIMIT`] facts.
    pub(crate) fn bound(&mut self) {
        self.0.truncate(LIMIT);
    }

    /// Forgets the facts that depend on the value of `l`.
    pub(crate) fn kill_local(&mut self, l: Local) {
        self.0.retain(|f| !f.mentions(l));
    }

    /// Forgets the facts that depend on what a place holds, for each place `which` accepts.
    pub(crate) fn kill_places(&mut self, which: impl Fn(Place) -> bool) {
        self.0.retain(|f| !f.place().is_some_and(&which));
    }

    /// Forgets which locals hold the same word as a place, for each place `which` accepts,
    /// while the length of what it holds stays known: copy-on-write gives the place a copy of
    /// the same length.
    pub(crate) fn kill_holds(&mut self, which: impl Fn(Place) -> bool) {
        self.0
            .retain(|f| !matches!(*f, Fact::Holds(_, p) if which(p)));
    }

    /// Forgets every length and every index in bounds.
    pub(crate) fn kill_lengths(&mut self) {
        self.0
            .retain(|f| !matches!(f, Fact::Len(..) | Fact::InBounds(..)));
    }

    /// Forgets the length of the list that each of `holders` holds, and every index in bounds
    /// of it.
    pub(crate) fn kill_lengths_of(&mut self, holders: &[Holder]) {
        self.0.retain(
            |f| !matches!(*f, Fact::Len(_, h) | Fact::InBounds(_, h) if holders.contains(&h)),
        );
    }

    /// Every holder of the list that the holders in `seed` hold, as the facts tell: those, each
    /// place that a local among them was read from, each local read from such a place, and so
    /// on.
    pub(crate) fn sharers(&self, seed: Vec<Holder>) -> Vec<Holder> {
        let mut out = seed;
        let mut next = 0;
        while let Some(&h) = out.get(next) {
            next += 1;
            let facts = match h {
                Holder::Local(l) => self.held_by(l),
                Holder::Place(_) => self.holding(),
            };
            for f in facts {
                let other = match (*f, h) {
                    (Fact::Holds(m, p), Holder::Local(l)) if m == l => Holder::Place(p),
                    (Fact::Holds(m, p), Holder::Place(q)) if p == q => Holder::Local(m),
                    _ => continue,
                };
                if !out.contains(&other) {
                    out.push(other);
                }
            }
        }
        out
    }

    /// Whether `t` is at least 0: known so, or an index in bounds of a list.
    pub(crate) fn nonneg(&self, t: Term) -> bool {
        match t {
            Term::Const(c) => c >= 0,
            Term::Local(_) => self.le(Term::Const(0), t) || self.indexes(t),
        }
    }

    /// `t`, and the terms known equal to it, as a copy and its source are while neither
    /// changes.
    fn equals(&self, t: Term) -> Vec<Term> {
        let mut out = vec![t];
        for f in self.above(t, false) {
            if out.len() > EQUALS {
                break;
            }
            if let Fact::Rel(Rel::Le(_, b)) = *f
                && !out.contains(&b)
                && self.contains(Fact::Rel(Rel::Le(b, t)))
            {
                out.push(b);
            }
        }
        out
    }

    /// Whether `t` is known to be an index in bounds of some list, so at least 0 and below the
    /// list's length.
    fn indexes(&self, t: Term) -> bool {
        self.equals(t)
            .into_iter()
            .any(|i| !self.bounds_of(i).is_empty())
    }

    /// Whether the relation is known to hold.
    pub(crate) fn holds(&self, r: Rel) -> bool {
        match r {
            Rel::Lt(a, b) => self.lt(a, b),
            Rel::Le(a, b) => self.le(a, b),
        }
    }

    /// Whether `a <= b` is known.
    pub(crate) fn le(&self, a: Term, b: Term) -> bool {
        a == b || self.related(a, b, false)
    }

    /// Whether `a < b` is known.
    pub(crate) fn lt(&self, a: Term, b: Term) -> bool {
        self.related(a, b, true)
    }

    /// Whether `low < high`, if `strict`, or `low <= high` is known, of the two terms or of
    /// terms known equal to them.
    fn related(&self, low: Term, high: Term, strict: bool) -> bool {
        let highs = self.equals(high);
        self.equals(low)
            .into_iter()
            .any(|l| highs.iter().any(|&h| self.related_as_stated(l, h, strict)))
    }

    /// Whether `low < high`, if `strict`, or `low <= high` is known: between constants,
    /// stated, or from two stated relations that meet at a term, at least one of them strict
    /// when `strict` is.
    fn related_as_stated(&self, low: Term, high: Term, strict: bool) -> bool {
        let stated = |x: Term, y: Term, s: bool| match (x, y) {
            (Term::Const(p), Term::Const(q)) => p < q || (!s && p == q),
            _ => {
                self.contains(Fact::Rel(Rel::Lt(x, y)))
                    || (!s && self.contains(Fact::Rel(Rel::Le(x, y))))
            }
        };
        stated(low, high, strict)
            || [true, false].into_iter().any(|lt| {
                self.above(low, lt).iter().any(|fact| {
                    let Fact::Rel(rel) = *fact else { return false };
                    let [_, middle] = rel.terms();
                    middle != high && stated(middle, high, strict && !lt)
                })
            })
    }

    /// The largest value `t` is known to have: its own, for a constant; and otherwise the least of
    /// what each relation to a constant, or to a term with such a relation, bounds it by, as a
    /// loop's counter below a size that a branch bounded is.
    pub(crate) fn upper(&self, t: Term) -> Option<i64> {
        self.bound_of(t, 2)
    }

    fn bound_of(&self, t: Term, depth: u32) -> Option<i64> {
        if let Term::Const(c) = t {
            return Some(c);
        }
        let through = |rel: Rel| -> Option<i64> {
            let (high, strict) = match rel {
                Rel::Lt(_, high) => (high, true),
                Rel::Le(_, high) => (high, false),
            };
            let bound = match high {
                Term::Const(c) => c,
                Term::Local(_) if depth > 0 => self.bound_of(high, depth - 1)?,
                Term::Local(_) => return None,
            };
            if strict {
                bound.checked_sub(1)
            } else {
                Some(bound)
            }
        };
        let stated = [true, false]
            .into_iter()
            .flat_map(|strict| self.above(t, strict));
        stated
            .filter_map(|f| match *f {
                Fact::Rel(rel) => through(rel),
                _ => None,
            })
            .min()
    }

    /// The least value `t` is known to have: its own, for a constant; and otherwise the largest of
    /// the constants it is stated at least, or above, and 0 when it is known not negative.
    pub(crate) fn lower(&self, t: Term) -> Option<i64> {
        if let Term::Const(c) = t {
            return Some(c);
        }
        let stated = self.iter().filter_map(|f| match f {
            Fact::Rel(Rel::Le(Term::Const(c), x)) if x == t => Some(c),
            Fact::Rel(Rel::Lt(Term::Const(c), x)) if x == t => c.checked_add(1),
            _ => None,
        });
        let zero = self.nonneg(t).then_some(0);
        stated.chain(zero).max()
    }

    /// Whether `x` is known to be below some integer: stated, at most a term that is, or an
    /// index in bounds of a list, which is below its length.
    pub(crate) fn below_another(&self, x: Term) -> bool {
        self.indexes(x) || self.below_stated(x)
    }

    /// Whether `x` is stated below some integer, or at most a term that is.
    fn below_stated(&self, x: Term) -> bool {
        let below = |y: Term| !self.above(y, true).is_empty();
        below(x)
            || self
                .above(x, false)
                .iter()
                .any(|f| matches!(*f, Fact::Rel(Rel::Le(_, m)) if m != x && below(m)))
    }

    /// The holders of the list in the local `l`: the local, and each place it was read from.
    pub(crate) fn holders(&self, l: Local) -> Vec<Holder> {
        let mut out = vec![Holder::Local(l)];
        out.extend(self.held_by(l).iter().filter_map(|f| match *f {
            Fact::Holds(_, p) => Some(Holder::Place(p)),
            _ => None,
        }));
        out
    }

    /// Whether `i` is known to be in bounds of the list that `h` holds: stated of it or of a
    /// term known equal to it, or known at least 0 and below the list's length.
    pub(crate) fn in_bounds(&self, i: Term, h: Holder) -> bool {
        self.equals(i)
            .into_iter()
            .any(|j| self.contains(Fact::InBounds(j, h)))
            || (self.nonneg(i)
                && self
                    .lengths()
                    .iter()
                    .any(|f| matches!(*f, Fact::Len(n, g) if g == h && self.lt(i, Term::Local(n)))))
    }
}
