//! The flow of values through a body, which locality and uniqueness read (modes.escaping,
//! modes.not-escaping and modes.copies and modes.shared-writes): where a binding's value, or a part
//! of it with a copy-on-write type, leaves the function, where a copy of it is made and what holds
//! the copy, and where a `var` or an `inout` parameter is written. The walk is in source order;
//! what it records happens at ticks, the points of the paths that execution may take, which
//! modes.shared-writes reads its conditions along (`super::paths`). Rule numbers in comments refer to
//! the Reference's chapter on modes, unless they name another record.

mod exprs;
mod places;

use std::collections::{HashMap, HashSet};

use stilt_hir::hir::{LocalId, Mode, Name};
use stilt_mir::FnRef;
use stilt_syntax::{TextRange, TextSize};
use stilt_types::tast::{Callee, Code, Pat};
use stilt_types::ty::Ty;

pub(crate) use super::Modification;
pub(crate) use places::{Step, overlap};

/// A point of the paths that execution may take: each goes on to the next unless the walk cuts
/// it, and jumps, branches and loops add steps of their own (modes.shared-writes).
pub(crate) type Tick = u32;

/// Past every position of a body: where what lasts for the rest of the function ends.
pub(crate) const END: TextSize = TextSize::new(u32::MAX);

/// How a binding's value leaves its function (modes.escaping).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum How {
    /// Returned by the function.
    Returned,
    /// Raised as an error.
    Raised,
    /// Yielded by a projection, which hands it to the caller (projections.yield).
    Yielded,
    /// Stored in another value.
    Stored(Stored),
    /// Assigned to a place of this other binding.
    Assigned(Name),
    /// Captured by a closure literal that escapes.
    Captured,
    /// Passed to a parameter that this function consumes.
    Consumed(FnRef),
}

/// The value a binding's value is stored in (modes.escaping).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stored {
    /// A record literal of this type.
    Record(Name),
    /// This variant's argument.
    Variant(Name),
    /// A tuple.
    Tuple,
    /// A list.
    List,
}

/// What the walk reads of the rest of the program.
pub(crate) trait Calls {
    /// The function that a call by name calls.
    fn callee(&self, c: &Callee) -> Option<FnRef>;
    /// The parameters of `f`, by their places, a receiver first, that it consumes.
    fn consumed(&self, f: &FnRef) -> Vec<usize>;
    /// Whether a type is copy-on-write (modes.copy-on-write-types).
    fn cow(&self, t: &Ty) -> bool;
    /// Whether a call may store an argument of type `from` in a value of one of `targets`, the
    /// types of its result and of its `inout` arguments (modes.call-stores).
    fn may_store(&self, from: &Ty, targets: &[Ty]) -> bool;
}

/// What declares a binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Let,
    Var,
    /// A parameter of the function or of a closure literal, with its mode.
    Param(Mode),
    /// A pattern of a `match`, an `if let`, a `for` or a `catch`.
    Pattern,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Decl {
    pub(crate) kind: Kind,
    /// The function, or the closure literal, whose binding it is.
    pub(crate) frame: u32,
    /// Its scope: where it starts and where it ends.
    pub(crate) scope: TextRange,
}

/// What holds a copy, which decides how long it lasts (modes.copies).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Holder {
    /// Bindings of a pattern, whose scope is there.
    Bound(Vec<LocalId>, TextRange),
    /// The binding that an assigned place is part of.
    Place(LocalId),
    /// Nothing a binding names, until there.
    Until(TextSize),
}

impl Holder {
    /// The bindings that hold the copy.
    pub(crate) fn bindings(&self) -> &[LocalId] {
        match self {
            Holder::Bound(bound, _) => bound,
            Holder::Place(root) => std::slice::from_ref(root),
            Holder::Until(_) => &[],
        }
    }
}

/// A copy of a part of a binding (modes.copies).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Copy {
    pub(crate) binding: LocalId,
    pub(crate) path: Vec<Step>,
    /// Where in the source it came into its holder.
    pub(crate) at_came: TextSize,
    /// The tick where it was made.
    pub(crate) made: Tick,
    /// The tick where it came into its holder: where it was made, or for a copy of a copy, where
    /// the later copy was made.
    pub(crate) came: Tick,
    pub(crate) holder: Holder,
    /// Whether it is stored in a value, captured or kept in a call's result, rather than bound
    /// by a pattern itself, so that it lasts for the rest of the function when what holds it
    /// escapes.
    pub(crate) stored: bool,
    /// The place inside the holder's value where the copy is, if it is one there: empty for a
    /// copy that is the holder's whole value.
    pub(crate) at: Option<Vec<Step>>,
    /// Whether copies of copies around a cycle may give the holder a deeper part, or the part at
    /// another place, than `path` and `at` say, so that it may hold a copy of any part below
    /// `path`.
    pub(crate) wide: bool,
}

/// A modification of a part of a binding, other than an assignment of all of it
/// (modes.kinds-of-access).
#[derive(Clone, Debug)]
pub(crate) struct Write {
    pub(crate) binding: LocalId,
    pub(crate) path: Vec<Step>,
    pub(crate) at: TextRange,
    pub(crate) tick: Tick,
    /// Whether it assigns the place, replacing what was there rather than writing inside it.
    pub(crate) replaces: bool,
    /// What modifies it.
    pub(crate) how: Modification,
}

/// An assignment of a binding or a place of it, which replaces the value there
/// (modes.shared-writes).
#[derive(Clone, Debug)]
pub(crate) struct Assigned {
    pub(crate) binding: LocalId,
    /// The path of the place assigned.
    pub(crate) path: Vec<Step>,
    /// The tick where its value starts, and the one where it is assigned.
    pub(crate) start: Tick,
    pub(crate) tick: Tick,
}

/// What the walk found of a body.
#[derive(Clone, Debug, Default)]
pub(crate) struct Flow {
    pub(crate) decls: HashMap<LocalId, Decl>,
    /// Each place where a binding that isn't a parameter escapes by itself.
    pub(crate) escapes: Vec<(LocalId, TextSize, How)>,
    /// Each closure literal that bindings hold, by its start, with the bindings it captures that
    /// aren't parameters: they escape there when one of the holders escapes (modes.not-escaping).
    pub(crate) held: Vec<(Vec<LocalId>, TextSize, Vec<LocalId>)>,
    pub(crate) copies: Vec<Copy>,
    pub(crate) writes: Vec<Write>,
    pub(crate) assigned: Vec<Assigned>,
    /// Each read of a place, by its root binding, at its tick.
    pub(crate) reads: Vec<(LocalId, Tick)>,
    /// Each part of a binding's own value that a value assigned to the whole binding holds: the
    /// binding, the part's path, its place inside the value if it has one, and where it is read
    /// (modes.shared-writes).
    pub(crate) selves: Vec<SelfPart>,
    /// Where each binding is bound, which starts it anew: a loop's next turn binds the bindings
    /// of its body again.
    pub(crate) bound: Vec<(LocalId, Tick)>,
    /// The paths of the body.
    pub(crate) paths: Steps,
    /// Each pair of names of one `when` whose values have the same type, which may be one place
    /// (modes.shared-when-names).
    pub(crate) joined: Vec<(LocalId, LocalId)>,
    /// Each call of `Shared.new`, as a write of the binding whose value it is given
    /// (modes.handles).
    pub(crate) handed: Vec<Write>,
}

/// The steps of the paths that execution may take through a body (modes.shared-writes).
#[derive(Clone, Debug, Default)]
pub(crate) struct Steps {
    /// Where in the source each tick is.
    pub(crate) at: Vec<TextSize>,
    /// The ticks that don't go on to the next one.
    pub(crate) cut: HashSet<Tick>,
    /// The ticks of `break`, `continue`, `return` and raises, which go only where their own
    /// steps say.
    pub(crate) jumps: HashSet<Tick>,
    /// The steps from one tick to another, other than to the next.
    pub(crate) links: Vec<(Tick, Tick)>,
    /// Each tick from the first to the second may go to the third: a raise to a `catch`, or a
    /// performance that isn't resumed to the end of its `with`.
    pub(crate) ranges: Vec<(Tick, Tick, Tick)>,
}

/// A part of a binding's own value that a value assigned to the whole binding holds: the
/// binding, the part's path, its place inside the value if it has one, and the tick where it is
/// read.
pub(crate) type SelfPart = (LocalId, Vec<Step>, Option<Vec<Step>>, Tick);

/// The flow of a body whose function has the parameters `params`, its locals named `names`.
pub(crate) fn flow(
    params: &[(Mode, LocalId)],
    names: &[Name],
    code: &Code,
    calls: &dyn Calls,
) -> Flow {
    let mut walk = exprs::Walk::new(calls, names);
    let whole = TextRange::new(TextSize::new(0), END);
    for &(mode, v) in params {
        walk.declare(v, Kind::Param(mode), whole);
    }
    walk.code(code);
    let mut flow = walk.flow;
    flow.join();
    flow
}

impl Flow {
    /// Makes each modification and read of a `when`'s name one of each name that may be its
    /// place too; an assignment of one replaces nothing of the others (modes.shared-when-names).
    fn join(&mut self) {
        let pairs = std::mem::take(&mut self.joined);
        let other = |v: LocalId, &(a, b): &(LocalId, LocalId)| {
            (v == a).then_some(b).or((v == b).then_some(a))
        };
        let mut writes = Vec::new();
        let mut reads = Vec::new();
        for pair in &pairs {
            for w in &self.writes {
                if let Some(u) = other(w.binding, pair) {
                    writes.push(Write {
                        binding: u,
                        ..w.clone()
                    });
                }
            }
            for &(v, tick) in &self.reads {
                if let Some(u) = other(v, pair) {
                    reads.push((u, tick));
                }
            }
        }
        self.writes.extend(writes);
        self.reads.extend(reads);
        self.joined = pairs;
    }
}

/// Where the value of an expression goes.
#[derive(Clone, Debug)]
struct Into<'t> {
    /// How a binding whose value is there leaves the function, if it does.
    leaves: Option<How>,
    /// What holds a copy of a value there, if one is made there: one bound, stored or assigned.
    held: Option<Holder>,
    /// What holds the result of a call that consumes the value there, which the callee may keep
    /// in it.
    result: Option<Holder>,
    /// The pattern that binds the value, whose parts it copies.
    pattern: Option<&'t Pat>,
    /// Until where a value there lasts when nothing holds it.
    lasts: TextSize,
    /// Where the value sits inside the value of what holds it, if it is a place there.
    at: Option<Vec<Step>>,
}

impl Into<'_> {
    /// A value that is only read, until `lasts`.
    fn read(lasts: TextSize) -> Self {
        Self {
            leaves: None,
            held: None,
            result: None,
            pattern: None,
            lasts,
            at: Some(Vec::new()),
        }
    }

    fn leaving(how: How) -> Self {
        Self {
            leaves: Some(how),
            ..Self::read(END)
        }
    }

    /// What holds a value made there, such as a literal or a closure.
    fn keeper(&self) -> Holder {
        if let Some(h) = self.held.as_ref().or(self.result.as_ref()) {
            return h.clone();
        }
        match self.leaves {
            Some(How::Returned | How::Raised | How::Yielded) => Holder::Until(END),
            _ => Holder::Until(self.lasts),
        }
    }
}
