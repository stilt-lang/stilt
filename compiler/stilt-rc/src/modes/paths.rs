//! The paths that execution may take through a body, which modes.shared-writes reads its
//! conditions along: from one tick of the flow to another, avoiding the ticks where a binding is
//! assigned or bound anew, and staying in a binding's scope once inside it. Each search goes
//! breadth first from a tick, once for each tick, what ends it and the scope it stays in.

use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};

use stilt_hir::hir::LocalId;
use stilt_syntax::TextRange;

use super::flow::{Assigned, Flow, Step, Tick};

/// What ends a path at a tick: nothing, an assignment of the whole binding or a binding of it
/// anew, or that or an assignment of a place of the binding that holds the place at the path.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum Kill {
    Nothing,
    Whole(LocalId),
    Covering(LocalId, Vec<Step>),
}

type Key = (Tick, Kill, Option<TextRange>);

/// The paths of a body.
pub(super) struct Paths<'f> {
    flow: &'f Flow,
    next: Vec<Vec<Tick>>,
    /// The assignments that end paths, by their ticks.
    assigned: HashMap<Tick, &'f Assigned>,
    bound: HashMap<Tick, Vec<LocalId>>,
    cache: RefCell<HashMap<Key, Vec<bool>>>,
}

impl<'f> Paths<'f> {
    /// The paths of a flow, ended by none of its assignments yet.
    pub(super) fn new(flow: &'f Flow) -> Self {
        let steps = &flow.paths;
        let n = steps.at.len() + 1;
        let mut next = vec![Vec::new(); n];
        let mut add = |a: Tick, b: Tick| {
            if let Some(out) = next.get_mut(a as usize) {
                out.push(b);
            }
        };
        for k in 0..n.saturating_sub(1) {
            let k = Tick::try_from(k).unwrap_or(Tick::MAX);
            if !steps.cut.contains(&k) {
                add(k, k + 1);
            }
        }
        for &(a, b) in &steps.links {
            add(a, b);
        }
        for &(first, last, out) in &steps.ranges {
            for k in first..=last {
                add(k, out);
            }
        }
        let mut bound: HashMap<Tick, Vec<LocalId>> = HashMap::new();
        for &(v, tick) in &flow.bound {
            bound.entry(tick).or_default().push(v);
        }
        Self {
            flow,
            next,
            assigned: HashMap::new(),
            bound,
            cache: RefCell::new(HashMap::new()),
        }
    }

    /// The same paths, which these assignments end. An assignment whose value holds the tick a
    /// path starts from doesn't end it.
    pub(super) fn ended_by(&self, assigned: &'f [Assigned]) -> Self {
        Self {
            flow: self.flow,
            next: self.next.clone(),
            assigned: assigned.iter().map(|a| (a.tick, a)).collect(),
            bound: self.bound.clone(),
            cache: RefCell::new(HashMap::new()),
        }
    }

    /// Whether `kill` ends a path from `from` at the tick `k`.
    fn ends(&self, kill: &Kill, from: Tick, k: Tick) -> bool {
        let binds = |v: &LocalId| self.bound.get(&k).is_some_and(|vs| vs.contains(v));
        let assigns = |v: &LocalId, covers: &dyn Fn(&[Step]) -> bool| {
            self.assigned.get(&k).is_some_and(|a| {
                a.binding == *v && covers(&a.path) && !(a.start <= from && from <= k)
            })
        };
        match kill {
            Kill::Nothing => false,
            Kill::Whole(v) => binds(v) || assigns(v, &<[Step]>::is_empty),
            Kill::Covering(v, at) => binds(v) || assigns(v, &|p: &[Step]| at.starts_with(p)),
        }
    }

    /// The ticks a path from `from` reaches: one may start outside `within` and enter it, but
    /// once inside it doesn't leave it.
    fn search(&self, kill: &Kill, within: Option<TextRange>, from: Tick) -> Vec<bool> {
        let n = self.next.len();
        let (mut seen, mut before) = (vec![false; n], vec![false; n]);
        let at = &self.flow.paths.at;
        let inside = |k: Tick| {
            within.is_none_or(|r| {
                at.get(k as usize)
                    .is_none_or(|&p| r.start() <= p && p <= r.end())
            })
        };
        let mut queue = VecDeque::new();
        let mut visit = |entered: bool, k: Tick, queue: &mut VecDeque<(Tick, bool)>| {
            let i = k as usize;
            if i >= n || self.ends(kill, from, k) {
                return;
            }
            if inside(k) {
                if !seen[i] {
                    seen[i] = true;
                    queue.push_back((k, true));
                }
            } else if !entered && !before[i] {
                before[i] = true;
                queue.push_back((k, false));
            }
        };
        let start = inside(from);
        for &k in self.next.get(from as usize).into_iter().flatten() {
            visit(start, k, &mut queue);
        }
        while let Some((k, entered)) = queue.pop_front() {
            for &j in &self.next[k as usize] {
                visit(entered, j, &mut queue);
            }
        }
        seen
    }

    /// Whether a path goes from the tick `a` to `b`, with no tick that `kill` ends after `a`, and
    /// that doesn't leave `within` once it is inside.
    pub(super) fn reaches(&self, kill: &Kill, within: Option<TextRange>, a: Tick, b: Tick) -> bool {
        let key = (a, kill.clone(), within);
        if let Some(seen) = self.cache.borrow().get(&key) {
            return seen.get(b as usize).copied().unwrap_or(false);
        }
        let seen = self.search(kill, within, a);
        let found = seen.get(b as usize).copied().unwrap_or(false);
        self.cache.borrow_mut().insert(key, seen);
        found
    }

    /// Whether any path goes from the tick `a` to `b`.
    pub(super) fn after(&self, a: Tick, b: Tick) -> bool {
        self.reaches(&Kill::Nothing, None, a, b)
    }
}
