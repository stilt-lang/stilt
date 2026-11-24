//! Where paths meet, and the paths that leave (facts.joins and facts.paths-that-leave).

use std::collections::BTreeSet;

use super::dbm::Term;
use super::state::{Renamed, Slot, State, common, meet};
use super::walker::Walker;
use crate::ty::Ty;

impl Walker<'_> {
    /// The facts where `states` meet (facts.joins): each binding whose current term, length or
    /// version differs between them takes a new one, which on each path equals that path's own.
    /// A contradictory path takes no part.
    pub(crate) fn join(&mut self, states: Vec<State>) -> State {
        let mut live: Vec<State> = Vec::with_capacity(states.len());
        let mut first = None;
        for s in states {
            if s.is_bottom() {
                first.get_or_insert(s);
            } else {
                live.push(s);
            }
        }
        match live.len() {
            0 => return first.unwrap_or_else(|| State::new(self.paths.capped)),
            1 => return live.pop().unwrap_or_else(|| State::new(self.paths.capped)),
            _ => {}
        }
        let paths: Vec<&State> = live.iter().collect();
        let mut out = live[0].clone();
        let mut renamed = Renamed::new();
        let mut terms = BTreeSet::new();
        for slot in [Slot::Int, Slot::Len, Slot::Ver] {
            let names: Vec<_> = paths[0]
                .slot(slot)
                .keys()
                .filter(|v| paths.iter().all(|p| p.slot(slot).contains_key(v)))
                .copied()
                .collect();
            out.slot_mut(slot).retain(|v, _| names.contains(v));
            for v in names {
                let owns: Vec<Term> = paths.iter().map(|p| p.slot(slot)[&v]).collect();
                if owns.iter().any(|t| *t != owns[0]) {
                    let j = self.fresh();
                    renamed.insert(j, owns);
                    out.slot_mut(slot).insert(v, j);
                    if slot != Slot::Ver {
                        terms.insert(j);
                    }
                }
            }
        }
        let mut target = common(&paths);
        target.extend(terms);
        out.facts = meet(target, &renamed, &paths);
        out
    }

    /// A `break` or a `continue`: the path goes to its loop's exit or head
    /// (facts.paths-that-leave).
    pub(crate) fn jump(&mut self, st: &mut State, back: bool) {
        let quiet = self.quiet;
        let target = self.paths.loops.iter().rposition(|f| f.real);
        if !st.is_bottom()
            && let Some(i) = target
            && self.paths.loops[i].level == quiet
        {
            let mut state = st.clone();
            if back && let Some(c) = self.paths.loops[i].counter {
                self.step(&mut state, c);
            }
            let frame = &mut self.paths.loops[i];
            if back {
                frame.continues.push(state);
            } else {
                frame.breaks.push(state);
            }
        }
        st.facts.unreached();
    }

    /// A path that may leave here, with the facts after the changes of facts.writes-through-calls
    /// and facts.map-keys: one that raises an `error` goes to the arms of the innermost `catch` of
    /// its type, and one that performs an operation, or calls code that may, to the end of each
    /// `with` around it whose handler takes control (facts.paths-that-leave).
    pub(crate) fn leaves(&mut self, st: &State, error: Option<&Ty>, effects: bool) {
        if st.is_bottom() {
            return;
        }
        let quiet = self.quiet;
        if let Some(error) = error
            && let Some((_, level, paths)) = self
                .paths
                .catches
                .iter_mut()
                .rev()
                .find(|(handled, _, _)| handled == error)
            && *level == quiet
        {
            paths.push(st.clone());
        }
        if effects {
            for (level, paths) in &mut self.paths.withs {
                if let Some(paths) = paths.as_mut().filter(|_| *level == quiet) {
                    paths.push(st.clone());
                }
            }
        }
    }
}
