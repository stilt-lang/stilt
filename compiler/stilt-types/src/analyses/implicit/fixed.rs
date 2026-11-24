//! The fixed points of the implicit effects (facts.inference): each body's summary, the items
//! that have each effect, and the recursive groups of the graph of what bodies name, whose
//! calls may not end (facts.div), and the items that have each capability (facts.capabilities).

use std::collections::{BTreeMap, BTreeSet};

use stilt_hir::hir::{Capabilities, Capability, Limits};

use super::{Effect, Fact, Key, Site, is_built_in};

/// Whether the code of a body has an effect itself: `None` when it doesn't, and otherwise the
/// first of its operations that has it, or `None` inside for a native function, whose call is
/// the operation.
pub(crate) type Own = Option<Option<Fact>>;

/// What the fixed points need of one body: its key, whether its own code can panic, allocates
/// or may not end, the items it names, whether its calls of itself descend, and what limits
/// it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Summary {
    pub(crate) key: Key,
    pub(crate) panics: Own,
    /// Whether its own code can panic when no check is proved, as a package's API reads it
    /// (versions.facts-without-proofs).
    pub(crate) panics_unproved: Own,
    /// An operation that can overflow (effects.overflow-effect).
    pub(crate) overflows: Own,
    pub(crate) allocates: Own,
    /// A `while` or a call through a stored function value (facts.div).
    pub(crate) diverges: Own,
    /// Whether its own code may not end when no loop is proved to end, as a package's API
    /// reads it (versions.facts-without-proofs).
    pub(crate) diverges_unproved: Own,
    /// A `when` (shared.locks).
    pub(crate) locks: Own,
    /// The capabilities of a native function (facts.capability-natives); no code has one of its
    /// own.
    pub(crate) capabilities: Capabilities,
    pub(crate) names: Vec<Key>,
    /// Whether every call of itself passes a strict part of one parameter
    /// (facts.descending-self-calls), or every one shrinks (facts.shrinking-recursion).
    pub(crate) descends: bool,
    /// Whether every call of itself passes a strict part of one parameter, with no proof.
    pub(crate) descends_unproved: bool,
    pub(crate) limits: Limits,
}

/// How an item has an effect.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Via {
    /// Its own code has it, through an operation, or as a native function.
    Own(Option<Fact>),
    /// It names an item that has it.
    Through(Key),
}

/// The items that have an effect, each with how it has it.
pub(crate) type Reached = BTreeMap<Key, Via>;

/// The implicit effects of the program's items and the standard library's.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Effects {
    pub(crate) panic: Reached,
    /// The items that can overflow (effects.overflow-effect).
    pub(crate) overflow: Reached,
    pub(crate) alloc: Reached,
    pub(crate) div: Reached,
    /// The items that hold shared values (shared.locks).
    pub(crate) locks: Reached,
    /// The items that have each capability, in the order of facts.capabilities.
    capabilities: [Reached; 8],
    /// Each item of a recursive group, an item that names itself among them, with its group.
    groups: BTreeMap<Key, usize>,
    /// The items whose calls of themselves descend (facts.descending-self-calls).
    descending: BTreeSet<Key>,
}

impl Effects {
    /// The items that have `effect`. This crate infers no `copy`.
    pub(crate) fn of(&self, effect: Effect) -> Option<&Reached> {
        match effect {
            Effect::Panic => Some(&self.panic),
            Effect::Overflow => Some(&self.overflow),
            Effect::Alloc => Some(&self.alloc),
            Effect::Div => Some(&self.div),
            Effect::Copy => None,
            Effect::Locks => Some(&self.locks),
            Effect::Capability(c) => Some(&self.capabilities[c as usize]),
        }
    }

    /// Whether the item `key` has `effect`. A built-in method allocates, and has no other
    /// effect.
    pub(crate) fn has(&self, effect: Effect, key: &Key) -> bool {
        self.of(effect).is_some_and(|r| r.contains_key(key))
            || (effect == Effect::Alloc && is_built_in(key))
    }

    /// The item whose own code gives `key` the effect, following the items it names, and the
    /// operation of that code that has it, unless the item is a native function.
    pub(crate) fn origin<'k>(
        &'k self,
        effect: Effect,
        mut key: &'k Key,
    ) -> (&'k Key, Option<&'k Fact>) {
        let Some(reached) = self.of(effect) else {
            return (key, None);
        };
        loop {
            match reached.get(key) {
                Some(Via::Through(next)) => key = next,
                Some(Via::Own(fact)) => return (key, fact.as_ref()),
                None => return (key, None),
            }
        }
    }

    /// Whether `site`, in the body of `caller`, may not end by naming `key` (facts.div):
    /// `key` is in the caller's recursive group, unless the site is a call of the caller
    /// itself, whose calls of itself descend.
    pub(crate) fn recurses(&self, caller: &Key, key: &Key, site: &Site) -> bool {
        match (self.groups.get(caller), self.groups.get(key)) {
            (Some(a), Some(b)) if a == b => {
                !(key == caller && site.called && self.descending.contains(caller))
            }
            _ => false,
        }
    }
}

/// The recursive groups of the graph of what each body names: its strongly connected
/// components of more than one item, and each item that names itself (facts.div). Each
/// item of a group is mapped to the group's index.
fn groups(summaries: &[Summary]) -> BTreeMap<Key, usize> {
    let index: BTreeMap<&Key, usize> = (0..).zip(summaries).map(|(i, s)| (&s.key, i)).collect();
    let edges: Vec<Vec<usize>> = summaries
        .iter()
        .map(|s| {
            s.names
                .iter()
                .filter_map(|k| index.get(k).copied())
                .collect()
        })
        .collect();
    let mut found = BTreeMap::new();
    for (g, component) in (0..).zip(components(&edges)) {
        let named_itself = |&i: &usize| edges[i].contains(&i);
        if component.len() > 1 || component.iter().any(named_itself) {
            for i in component {
                found.insert(summaries[i].key.clone(), g);
            }
        }
    }
    found
}

/// The strongly connected components of a graph, by Tarjan's algorithm, without recursion.
fn components(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = edges.len();
    let (mut order, mut low) = (vec![usize::MAX; n], vec![0; n]);
    let (mut on, mut stack, mut found, mut next) = (vec![false; n], Vec::new(), Vec::new(), 0);
    for root in 0..n {
        if order[root] != usize::MAX {
            continue;
        }
        let mut work = vec![(root, 0)];
        while let Some(&mut (v, ref mut child)) = work.last_mut() {
            if *child == 0 {
                (order[v], low[v]) = (next, next);
                next += 1;
                stack.push(v);
                on[v] = true;
            }
            if let Some(&w) = edges[v].get(*child) {
                *child += 1;
                if order[w] == usize::MAX {
                    work.push((w, 0));
                } else if on[w] {
                    low[v] = low[v].min(order[w]);
                }
                continue;
            }
            work.pop();
            if let Some(&(parent, _)) = work.last() {
                low[parent] = low[parent].min(low[v]);
            }
            if low[v] == order[v] {
                let mut component = Vec::new();
                while let Some(w) = stack.pop() {
                    on[w] = false;
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                found.push(component);
            }
        }
    }
    found
}

/// What a body's own code has of `effect`: a native function has its capabilities as its own,
/// whose call is the operation (facts.capability-natives).
fn own(s: &Summary, effect: Effect) -> Own {
    match effect {
        Effect::Panic => s.panics.clone(),
        Effect::Overflow => s.overflows.clone(),
        Effect::Alloc => s.allocates.clone(),
        Effect::Div | Effect::Copy => s.diverges.clone(),
        Effect::Locks => s.locks.clone(),
        Effect::Capability(c) => s.capabilities.has(c).then_some(None),
    }
}

/// facts.inference: the items that have `effect`, as a least fixed point over the items that each
/// body names. An item that a `without` limits counts as one without the effect, since its own
/// operations are errors where they are written (effects.without-panic; facts.without-alloc;
/// facts.without-div). Each item found keeps the item it has the effect through, found in an
/// earlier round, so that following them always ends at an item whose own code has it, which keeps
/// its operation.
pub(crate) fn reach(summaries: &[Summary], effect: Effect) -> Reached {
    let counted: Vec<&Summary> = summaries
        .iter()
        .filter(|s| !effect.limited(s.limits))
        .collect();
    let mut reached = Reached::new();
    loop {
        let has = |k: &Key| reached.contains_key(k) || (effect == Effect::Alloc && is_built_in(k));
        let found: Vec<(Key, Via)> = counted
            .iter()
            .filter(|s| !reached.contains_key(&s.key))
            .filter_map(|s| {
                if let Some(fact) = own(s, effect) {
                    return Some((s.key.clone(), Via::Own(fact)));
                }
                let through = s.names.iter().find(|k| has(k))?;
                Some((s.key.clone(), Via::Through(through.clone())))
            })
            .collect();
        if found.is_empty() {
            return reached;
        }
        reached.extend(found);
    }
}

/// The implicit effects of every item when verification proves nothing, as [`effects`] finds them
/// with its proofs: the limitable facts of a package's API (versions.limitable-facts;
/// versions.facts-without-proofs).
pub(crate) fn unproved(summaries: &[Summary]) -> Effects {
    let unproved: Vec<Summary> = (summaries.iter())
        .map(|s| Summary {
            panics: s.panics_unproved.clone(),
            diverges: s.diverges_unproved.clone(),
            descends: s.descends_unproved,
            ..s.clone()
        })
        .collect();
    effects(&unproved)
}

/// facts.div: a body whose own code has no other `div` may not end when it calls an item
/// of its recursive group, or itself without descending.
fn with_recursion(summaries: &[Summary], groups: &BTreeMap<Key, usize>) -> Vec<Summary> {
    summaries
        .iter()
        .map(|s| {
            let Some(g) = groups.get(&s.key) else {
                return s.clone();
            };
            let others = s
                .names
                .iter()
                .any(|k| *k != s.key && groups.get(k) == Some(g));
            let fact = if others {
                Fact::definite("a call back into its recursive group".to_owned())
            } else if !s.descends {
                Fact::definite("a recursive call on no part of a parameter".to_owned())
            } else {
                return s.clone();
            };
            Summary {
                diverges: s.diverges.clone().or(Some(Some(fact))),
                ..s.clone()
            }
        })
        .collect()
}

/// The implicit effects of every item, given every body's summary.
pub(crate) fn effects(summaries: &[Summary]) -> Effects {
    let groups = groups(summaries);
    let recursive = with_recursion(summaries, &groups);
    Effects {
        panic: reach(summaries, Effect::Panic),
        overflow: reach(summaries, Effect::Overflow),
        alloc: reach(summaries, Effect::Alloc),
        div: reach(&recursive, Effect::Div),
        locks: reach(summaries, Effect::Locks),
        capabilities: Capability::ALL.map(|c| reach(summaries, Effect::Capability(c))),
        descending: summaries
            .iter()
            .filter(|s| s.descends)
            .map(|s| s.key.clone())
            .collect(),
        groups,
    }
}
