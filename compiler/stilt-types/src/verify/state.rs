//! What the analysis knows at a point of a body: its facts, and each binding's current term, length
//! and version (facts.terms, facts.difference-facts and facts.map-keys), with the joins of
//! facts.joins.

use std::collections::{BTreeMap, BTreeSet};

use stilt_hir::hir::LocalId;

use super::dbm::{Facts, Key, Term, ZERO};

/// The facts at a point, and the current term of each integer binding, the current length of
/// each list binding and the version of each binding of another type, a list's among them.
#[derive(Clone, Debug)]
pub(crate) struct State {
    pub(crate) facts: Facts,
    pub(crate) ints: BTreeMap<LocalId, Term>,
    pub(crate) lens: BTreeMap<LocalId, Term>,
    pub(crate) vers: BTreeMap<LocalId, Term>,
}

/// Which of a binding's terms a join or a loop's head gives a new one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Slot {
    Int,
    Len,
    Ver,
}

impl State {
    pub(crate) fn new(capped: bool) -> Self {
        Self {
            facts: Facts::new(capped),
            ints: BTreeMap::new(),
            lens: BTreeMap::new(),
            vers: BTreeMap::new(),
        }
    }

    pub(crate) fn is_bottom(&self) -> bool {
        self.facts.is_bottom()
    }

    /// The bindings' terms of one slot.
    pub(crate) fn slot(&self, s: Slot) -> &BTreeMap<LocalId, Term> {
        match s {
            Slot::Int => &self.ints,
            Slot::Len => &self.lens,
            Slot::Ver => &self.vers,
        }
    }

    pub(crate) fn slot_mut(&mut self, s: Slot) -> &mut BTreeMap<LocalId, Term> {
        match s {
            Slot::Int => &mut self.ints,
            Slot::Len => &mut self.lens,
            Slot::Ver => &mut self.vers,
        }
    }

    /// Every binding's current term, length and version.
    pub(crate) fn current(&self) -> impl Iterator<Item = Term> + '_ {
        self.ints
            .values()
            .chain(self.lens.values())
            .chain(self.vers.values())
            .copied()
    }

    /// Forgets the bindings that `keep` doesn't hold: those whose scope has ended.
    pub(crate) fn scope_to(&mut self, keep: &Bindings) {
        self.ints.retain(|v, _| keep.ints.contains(v));
        self.lens.retain(|v, _| keep.lens.contains(v));
        self.vers.retain(|v, _| keep.vers.contains(v));
    }

    /// The bindings in scope.
    pub(crate) fn bindings(&self) -> Bindings {
        Bindings {
            ints: self.ints.keys().copied().collect(),
            lens: self.lens.keys().copied().collect(),
            vers: self.vers.keys().copied().collect(),
        }
    }

    /// Drops the presence of keys at versions that no binding holds and no evaluation has read,
    /// and of keys at such versions, then every term but those of `keep`, the bindings' current
    /// ones and the terms of the keys still present (facts.difference-facts).
    pub(crate) fn drop_terms(&mut self, keep: &BTreeSet<Term>) {
        let live: BTreeSet<Term> = self.current().chain(keep.iter().copied()).collect();
        self.facts.present.retain(|(version, key)| {
            live.contains(version) && !matches!(key, Key::Version(v) if !live.contains(v))
        });
        let mut kept = live;
        for (_, key) in &self.facts.present {
            if let Key::Form(t, _) = key {
                kept.insert(*t);
            }
        }
        self.facts.keep(&|t| kept.contains(&t));
    }
}

/// The bindings in scope at a point, by the terms they have.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Bindings {
    pub(crate) ints: BTreeSet<LocalId>,
    pub(crate) lens: BTreeSet<LocalId>,
    pub(crate) vers: BTreeSet<LocalId>,
}

/// A term of a join, with the term it stands for on each path, in the paths' order.
pub(crate) type Renamed = BTreeMap<Term, Vec<Term>>;

/// The term that `t`, of a join, stands for on path `p`: its own there, or itself.
pub(crate) fn own(renamed: &Renamed, p: usize, t: Term) -> Term {
    renamed.get(&t).map_or(t, |owns| owns[p])
}

/// The facts where the paths meet, each binding of `env` taking, on each path, the term the path
/// gives it (facts.joins): pair by pair, the greatest `c`; a term non-zero, and a key present at a
/// version, when on every path its own is. `target` holds the terms of the result, in increasing
/// order, `renamed` those that stand for a term of each path's own. No path is contradictory.
pub(crate) fn meet(target: Vec<Term>, renamed: &Renamed, paths: &[&State]) -> Facts {
    let owns: Vec<Box<dyn Fn(Term) -> Term + '_>> = (0..paths.len())
        .map(|p| Box::new(move |t| own(renamed, p, t)) as Box<dyn Fn(Term) -> Term>)
        .collect();
    let with: Vec<(&Facts, &dyn Fn(Term) -> Term)> = paths
        .iter()
        .zip(&owns)
        .map(|(s, f)| (&s.facts, &**f))
        .collect();
    let mut facts = Facts::merge(target, &with);
    facts.present = present(&facts, renamed, paths);
    facts
}

/// The keys present at the join: those present on the first path, read as each term of the
/// join that stands for its terms there, that are present on every path.
fn present(facts: &Facts, renamed: &Renamed, paths: &[&State]) -> BTreeSet<(Term, Key)> {
    let mut versions: BTreeSet<Term> = paths[0].current().collect();
    versions.extend(renamed.keys().copied());
    versions.extend(paths[0].facts.present.iter().map(|(v, _)| *v));
    let standing = |first: Term, terms: &mut dyn Iterator<Item = Term>| -> Vec<Term> {
        terms.filter(|t| own(renamed, 0, *t) == first).collect()
    };
    let mut found = BTreeSet::new();
    for (version, key) in &paths[0].facts.present {
        for v in standing(*version, &mut versions.iter().copied()) {
            let keys: Vec<Key> = match key {
                Key::Form(t, d) => standing(*t, &mut facts.terms().iter().copied())
                    .into_iter()
                    .map(|t| Key::Form(t, *d))
                    .collect(),
                Key::Version(k) => standing(*k, &mut versions.iter().copied())
                    .into_iter()
                    .map(Key::Version)
                    .collect(),
                Key::Text(_) => vec![key.clone()],
            };
            for k in keys {
                let everywhere = (1..paths.len()).all(|p| {
                    let k_p = match &k {
                        Key::Form(t, d) => Key::Form(own(renamed, p, *t), *d),
                        Key::Version(w) => Key::Version(own(renamed, p, *w)),
                        Key::Text(s) => Key::Text(s.clone()),
                    };
                    paths[p].facts.present.contains(&(own(renamed, p, v), k_p))
                });
                if everywhere {
                    found.insert((v, k));
                }
            }
        }
    }
    found
}

/// The terms that every path's facts hold, which a join keeps as they are.
pub(crate) fn common(paths: &[&State]) -> Vec<Term> {
    let mut out: Vec<Term> = paths[0].facts.terms().to_vec();
    for p in &paths[1..] {
        out.retain(|t| p.facts.has(*t));
    }
    debug_assert_eq!(out.first(), Some(&ZERO));
    out
}
