//! Shared writes (modes.copies and modes.shared-writes): the modifications of a `var` binding or an
//! `inout` parameter while a copy of the modified part, or a copy of that copy, may still last,
//! along the paths that execution may take ([`Paths`]).

use std::collections::HashMap;

use stilt_hir::hir::{LocalId, Mode};
use stilt_syntax::{TextRange, TextSize};

use super::flow::{
    Assigned, Copy, END, Flow, Holder, How, Kind, Modification, Step, Tick, Write, overlap,
};
use super::paths::{Kill, Paths};

/// A shared modification: the binding, where it is, the binding that holds the copy that makes
/// it shared, if one does, and what the modification is.
pub(super) type Found = (LocalId, TextRange, Option<LocalId>, Modification);

/// Each shared modification, where it is, with the binding that holds the copy that makes it
/// shared, if one does.
pub(super) fn shared(flow: &Flow, escapes: &HashMap<LocalId, (TextSize, How)>) -> Vec<Found> {
    let all = Paths::new(flow);
    let copies = transitive(&all, &flow.copies);
    let (own, assigned): (Vec<Assigned>, Vec<Assigned>) = flow
        .assigned
        .iter()
        .cloned()
        .partition(|a| holds_own(&all, flow, &copies, a));
    let paths = all.ended_by(&assigned);
    let rules = Rules {
        flow,
        paths: &paths,
        own: &own,
        escapes,
    };
    flow.writes
        .iter()
        .filter(|w| {
            flow.decls
                .get(&w.binding)
                .is_some_and(|d| matches!(d.kind, Kind::Var | Kind::Param(Mode::Inout)))
        })
        .filter_map(|w| {
            if let Some(copy) = copies.iter().find(|c| rules.sharing(c, w)) {
                let with = copy.holder.bindings().first().copied();
                return Some((w.binding, w.at, with, w.how));
            }
            let with = copies.iter().find_map(|c| rules.mirrored(c, w))?;
            Some((w.binding, w.at, Some(with), w.how))
        })
        .chain(flow.handed.iter().filter_map(|w| {
            rules
                .handed(w)
                .then_some((w.binding, w.at, None, Modification::NewHandle))
        }))
        .collect()
}

/// What the rules read of a body: its flow, its paths, which the assignments of whole bindings
/// end, those that hold a part of their own binding's value, `own`, and where its bindings
/// escape.
struct Rules<'a> {
    flow: &'a Flow,
    paths: &'a Paths<'a>,
    own: &'a [Assigned],
    escapes: &'a HashMap<LocalId, (TextSize, How)>,
}

impl Rules<'_> {
    /// Whether an assignment of the whole of `v` whose value holds a part of `v`'s own value is
    /// on a path from the tick `from` to `until`: after it, a copy made before it counts as a copy
    /// of every part of `v` (modes.shared-writes).
    fn reshaped(&self, v: LocalId, from: Tick, until: Tick) -> bool {
        self.own.iter().any(|a| {
            a.binding == v && self.paths.after(from, a.tick) && self.paths.after(a.tick, until)
        })
    }

    /// Where a copy lasts along a path from where it came into its holder (modes.copies): the
    /// scope of the binding that holds it, the whole body when what holds it escapes, or none
    /// past where its holder lets it go.
    fn region(&self, c: &Copy) -> Option<TextRange> {
        let whole = TextRange::new(TextSize::new(0), END);
        let escapes = |h: &LocalId| self.escapes.contains_key(h);
        match &c.holder {
            Holder::Bound(holders, _) if c.stored && holders.iter().any(escapes) => Some(whole),
            Holder::Bound(_, scope) => Some(*scope),
            Holder::Place(root) if escapes(root) => Some(whole),
            Holder::Place(root) => Some(self.flow.decls.get(root).map_or(whole, |d| d.scope)),
            Holder::Until(end) if *end == END => Some(whole),
            Holder::Until(end) => (c.at_came <= *end).then(|| TextRange::new(c.at_came, *end)),
        }
    }

    /// Whether a copy shares the part a write modifies (modes.shared-writes): it copies the part,
    /// and a path from where it was made reaches the write while it lasts, with no assignment of
    /// the whole binding, and no binding of it anew, on the way.
    fn sharing(&self, c: &Copy, w: &Write) -> bool {
        let parts = overlap(&c.path, &w.path) || self.reshaped(w.binding, c.made, w.tick);
        if c.binding != w.binding || !parts {
            return false;
        }
        let Some(within) = self.region(c) else {
            return false;
        };
        let within = Some(within);
        let kill = Kill::Whole(w.binding);
        (c.made == c.came || self.paths.reaches(&kill, None, c.made, c.came))
            && self.paths.reaches(&kill, within, c.came, w.tick)
    }

    /// Whether a call of `Shared.new`, `w`, shares the value of a binding that might still read it
    /// after the call: a parameter, which its caller reads, or a binding read on a path from the
    /// call (modes.handles).
    fn handed(&self, w: &Write) -> bool {
        let kill = Kill::Whole(w.binding);
        let parameter = self
            .flow
            .decls
            .get(&w.binding)
            .is_some_and(|d| matches!(d.kind, Kind::Param(_)));
        parameter
            || self
                .flow
                .reads
                .iter()
                .any(|&(u, at)| u == w.binding && self.paths.reaches(&kill, None, w.tick, at))
    }

    /// Whether `v` might still read the value it had at the tick `from` after the write `w`: a
    /// path from `from` reaches `w` with no assignment of `v`'s whole, and no binding of it anew,
    /// on the way, and goes on to a read of `v`, or `v` is read when the body of `w` ends: an
    /// `inout` parameter of that body, which goes back to its caller, or a binding of an enclosing
    /// body that it captures, which the closure's next call reads; or `w` is a modification that
    /// starts a call, which reads `v` after it when `v` is the root of one of its `inout`
    /// arguments.
    fn read_after(&self, v: LocalId, from: Tick, w: &Write) -> bool {
        let kill = Kill::Whole(v);
        let frame = self.flow.decls.get(&w.binding).map(|d| d.frame);
        let at_end = self.flow.decls.get(&v).is_some_and(|d| match d.kind {
            Kind::Param(Mode::Inout) => Some(d.frame) == frame,
            _ => Some(d.frame) != frame,
        });
        let by_the_call =
            |&(u, first, read): &(LocalId, Tick, Tick)| u == v && first <= w.tick && w.tick < read;
        self.paths.reaches(&kill, None, from, w.tick)
            && (at_end
                || self.flow.inout_reads.iter().any(by_the_call)
                || self
                    .flow
                    .reads
                    .iter()
                    .any(|&(u, at)| u == v && self.paths.reaches(&kill, None, w.tick, at)))
    }

    /// The part of the copied binding that `w` modifies, when it reaches inside the copy `c` that
    /// its binding holds, as its value or at a place inside it: a path from where the copy came
    /// there reaches `w` with no assignment to the place that holds it, and no binding of the
    /// binding anew, on the way. An assignment replaces a copy at its own place rather than
    /// writing inside it. After an assignment of the whole binding that holds a part of its own
    /// value, or when copies of copies may have given the binding any part, the write may reach
    /// anywhere inside the copy.
    fn reached(&self, c: &Copy, w: &Write) -> Option<Vec<Step>> {
        let at = c.at.as_ref()?;
        if c.binding == w.binding || !c.holder.bindings().contains(&w.binding) {
            return None;
        }
        let kill = Kill::Covering(w.binding, at.clone());
        if !self.paths.reaches(&kill, None, c.came, w.tick) {
            return None;
        }
        if c.wide || self.reshaped(w.binding, c.came, w.tick) {
            return Some(c.path.clone());
        }
        let inside = w.path.starts_with(at) && !(w.replaces && at.len() >= w.path.len());
        inside.then(|| c.path.iter().chain(&w.path[at.len()..]).cloned().collect())
    }

    /// The binding that makes a write shared from the other side (modes.shared-writes): the write
    /// reaches inside a copy of another binding's part that its binding holds, and that binding,
    /// or another binding that holds a copy of the part, might still read it. A copy made on a
    /// path through an assignment of the whole copied binding that holds a part of its own value,
    /// before or after the copy the write reaches, may be of any part of it.
    fn mirrored(&self, c: &Copy, w: &Write) -> Option<LocalId> {
        let part = self.reached(c, w)?;
        if self.read_after(c.binding, c.made, w) {
            return Some(c.binding);
        }
        let held = |d: &Copy| d.holder.bindings().contains(&w.binding);
        let any = |d: &Copy| {
            self.reshaped(c.binding, c.made, d.made) || self.reshaped(c.binding, d.made, c.made)
        };
        self.flow
            .copies
            .iter()
            .filter(|d| d.binding == c.binding && !held(d))
            .filter(|d| overlap(&d.path, &part) || any(d))
            .find_map(|d| {
                let holders = d.holder.bindings().iter();
                holders.copied().find(|&h| self.read_after(h, d.made, w))
            })
    }
}

/// Every copy, with the copies of copies (modes.copies): a copy that a binding holds goes wherever
/// a copy of that binding's part that holds it, made on a path after it, goes, and is a copy of
/// the first binding there, held by what holds the later copy. It counts from where the first
/// binding's value was copied, which is what an assignment of the whole binding is measured
/// against (modes.shared-writes). A copy found again at another place inside its holder, or of a
/// part inside a part it is a copy of already, is the same copy, so that copies passed around a
/// cycle of bindings end; the copy found first may then hold any part below its path.
fn transitive(paths: &Paths<'_>, found: &[Copy]) -> Vec<Copy> {
    let mut all = found.to_vec();
    let mut next = 0;
    while next < all.len() {
        let c = all[next].clone();
        next += 1;
        let carried = |d: &&Copy| {
            c.holder.bindings().contains(&d.binding)
                && d.made != c.came
                && paths.after(c.came, d.made)
                && !d.holder.bindings().contains(&c.binding)
        };
        let derived: Vec<Copy> = found
            .iter()
            .filter(carried)
            .filter_map(|d| {
                let (path, at) = within(d, &c)?;
                Some(Copy {
                    path,
                    at_came: d.at_came,
                    came: d.made,
                    holder: d.holder.clone(),
                    stored: d.stored,
                    at,
                    ..c.clone()
                })
            })
            .collect();
        for d in derived {
            let same = |e: &Copy| {
                e.binding == d.binding
                    && e.made == d.made
                    && e.came == d.came
                    && e.holder == d.holder
                    && e.stored == d.stored
                    && d.path.starts_with(&e.path)
            };
            match all.iter().position(same) {
                Some(i) => {
                    let e = &mut all[i];
                    e.wide |= e.path != d.path || e.at != d.at;
                }
                None => all.push(d),
            }
        }
    }
    all
}

/// A copy's path, and its place inside its holder if it is at one.
type Within = (Vec<Step>, Option<Vec<Step>>);

/// The copy `c` as the holder of `d`, a later copy of a part of `c`'s holder, holds it: its path
/// and its place there. The part holds the copy, or lies inside it and is a copy of a part of the
/// copied binding; a part beside the copy holds none of it. A copy at no known place in its holder
/// may be in any part.
fn within(d: &Copy, c: &Copy) -> Option<Within> {
    let Some(inner) = &c.at else {
        return Some((c.path.clone(), None));
    };
    if inner.starts_with(&d.path) {
        let rest = &inner[d.path.len()..];
        let at = d.at.as_ref().map(|outer| [outer.as_slice(), rest].concat());
        return Some((c.path.clone(), at));
    }
    d.path.starts_with(inner).then(|| {
        let path = [c.path.as_slice(), &d.path[inner.len()..]].concat();
        (path, d.at.clone())
    })
}

/// Whether an assignment of the whole of a binding holds a part of its own value, read from the
/// binding or from another binding that holds a copy of it, so that it is no assignment of the
/// whole for the rule (modes.shared-writes).
fn holds_own(paths: &Paths<'_>, flow: &Flow, copies: &[Copy], a: &Assigned) -> bool {
    let u = a.binding;
    let within = |k: Tick| a.start <= k && k <= a.tick;
    let holds_copy = |r: LocalId, made: Tick| {
        r == u
            || copies.iter().any(|c| {
                c.binding == u
                    && c.holder.bindings().contains(&r)
                    && c.came != made
                    && paths.after(c.came, made)
            })
    };
    a.path.is_empty()
        && (flow.selves.iter().any(|(v, _, _, k)| *v == u && within(*k))
            || flow.copies.iter().any(|c| {
                c.holder.bindings().contains(&u) && within(c.made) && holds_copy(c.binding, c.made)
            }))
}
