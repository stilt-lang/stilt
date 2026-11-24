//! What the walk of a body records (facts.rules-of-acceptance): the writes of each body's own code,
//! the tests and stores that give facts to the code they guard, the parts of the code that hold
//! writes, the `for` loops over ranges, and the operations and loops that the rules read, with what
//! is around each where it is.

use std::collections::{BTreeSet, HashMap};

use stilt_hir::hir::{BinaryOp, LocalId, Name};
use stilt_syntax::{TextRange, TextSize};

use super::code::Atom;
use crate::tast::{Arg, Block, Expr, ExprKind};
use crate::verify::Check;

/// What a write does to the place it writes (facts.rules-of-acceptance).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum WriteKind {
    Assign(Option<BinaryOp>),
    Inout,
    /// The receiver of `Map.insert`, which stores into the map (facts.keys).
    Insert,
    Yield,
}

/// A write of a body's own code: an assignment, an `inout` argument or receiver, or a `yield`,
/// of a place rooted in a binding, by the fields after the binding before any index.
pub(super) struct Write<'a> {
    pub(super) body: u32,
    pub(super) root: LocalId,
    pub(super) fields: Vec<Name>,
    /// Whether the place goes through an index or a tuple's element past those fields.
    pub(super) indexed: bool,
    pub(super) kind: WriteKind,
    /// An assignment's right side.
    pub(super) value: Option<&'a Expr>,
    pub(super) at: TextSize,
}

impl Write<'_> {
    /// Whether it changes the length of the list at `p`: it writes `p` or a place that `p`
    /// extends, and not through an element (facts.rules-of-acceptance).
    pub(super) fn changes(&self, p: &super::code::Place) -> bool {
        !self.indexed && self.root == p.root && p.fields.starts_with(&self.fields)
    }

    /// Whether it changes the map at `p` other than by storing into it (facts.keys).
    pub(super) fn unstores(&self, p: &super::code::Place) -> bool {
        self.changes(p) && !(self.kind == WriteKind::Insert && self.fields == p.fields)
    }
}

/// A test, or a statement that stores a key, with the facts it gives the code after it, where
/// the log stood before it and its number among tests and loops.
pub(super) struct Frame {
    pub(super) atoms: Vec<Atom>,
    pub(super) start: usize,
    pub(super) id: u32,
}

/// The writes that a part of the code holds, as a range of the log.
#[derive(Clone, Copy, Debug)]
pub(super) struct Span {
    pub(super) start: usize,
    pub(super) end: usize,
}

/// A `for` over a range whose pattern is a binding (facts.range-loops).
pub(super) struct Range<'a> {
    pub(super) body: u32,
    pub(super) var: LocalId,
    pub(super) start: &'a Expr,
    pub(super) end: &'a Expr,
    pub(super) inclusive: bool,
    /// The span of its body.
    pub(super) span: usize,
}

/// An operation that a rule may prove.
pub(super) enum Op<'a> {
    /// `base[key]`.
    Index(&'a Expr, &'a Expr),
    /// A division by the divisor.
    Division(&'a Expr),
    /// A call of the body's function, with its arguments.
    SelfCall(&'a [Arg]),
}

/// An operation, with what is around it where it is.
pub(super) struct Pending<'a> {
    pub(super) op: Op<'a>,
    pub(super) at: TextRange,
    pub(super) check: Option<Check>,
    pub(super) body: u32,
    pub(super) log_at: usize,
    /// The frames that guard it, outermost first.
    pub(super) frames: Vec<usize>,
    /// The loops of its body that hold it, by number and span.
    pub(super) loops: Vec<(u32, usize)>,
    /// The innermost statement of its body that holds it.
    pub(super) stmt: Option<usize>,
    /// The `for` loops over ranges around it, in any body, outermost first.
    pub(super) ranges: Vec<usize>,
}

/// A `while`, or a `loop`, which has no condition (facts.counting-loops).
pub(super) struct Looped<'a> {
    pub(super) at: TextRange,
    pub(super) body: u32,
    pub(super) cond: Option<&'a Expr>,
    pub(super) block: &'a Block,
    pub(super) span: usize,
}

/// How a binding is declared, for its known sign (facts.known-signs).
pub(super) enum Declared<'a> {
    Let(&'a Expr),
    Var(&'a Expr),
    /// The variable of a `for` over a range, with its start.
    Range(&'a Expr),
}

/// What the walk records.
pub(super) struct Walked<'a> {
    pub(super) log: Vec<Write<'a>>,
    pub(super) spans: Vec<Span>,
    pub(super) frames: Vec<Frame>,
    pub(super) ranges: Vec<Range<'a>>,
    pub(super) pending: Vec<Pending<'a>>,
    pub(super) loops: Vec<Looped<'a>>,
    pub(super) decls: HashMap<LocalId, (u32, Declared<'a>)>,
    pub(super) whens: BTreeSet<LocalId>,
}

impl<'a> Walked<'a> {
    /// The writes of the body `body` in the span `span`.
    pub(super) fn in_span(&self, body: u32, span: usize) -> impl Iterator<Item = &Write<'a>> {
        let Span { start, end } = self.spans[span];
        self.log[start..end].iter().filter(move |w| w.body == body)
    }

    /// The writes between the frame `frame` and the operation `p` (facts.rules-of-acceptance):
    /// those since the frame's test, those of the loops inside its code that hold the operation,
    /// and those of the statement that holds it.
    pub(super) fn between(&self, frame: usize, p: &Pending<'a>) -> Vec<&Write<'a>> {
        let f = &self.frames[frame];
        let mut out: Vec<&Write<'a>> = self.log[f.start..p.log_at]
            .iter()
            .filter(|w| w.body == p.body)
            .collect();
        for &(id, span) in &p.loops {
            if id > f.id {
                out.extend(self.in_span(p.body, span));
            }
        }
        if let Some(s) = p.stmt {
            out.extend(self.in_span(p.body, s));
        }
        out
    }

    /// The innermost frame guarding `p` that gives a fact `holds` accepts.
    pub(super) fn frame(&self, p: &Pending<'_>, holds: &dyn Fn(&Atom) -> bool) -> Option<usize> {
        p.frames
            .iter()
            .rev()
            .copied()
            .find(|&f| self.frames[f].atoms.iter().any(holds))
    }
}

/// The binding that roots a place, the fields after it before any index or tuple's element,
/// and whether one follows them.
pub(super) fn path(place: &Expr) -> Option<(LocalId, Vec<Name>, bool)> {
    match &place.kind {
        ExprKind::Local(v) => Some((*v, Vec::new(), false)),
        ExprKind::Field(base, name) => {
            let (root, mut fields, indexed) = path(base)?;
            if !indexed {
                fields.push(*name);
            }
            Some((root, fields, indexed))
        }
        ExprKind::Index(base, _) | ExprKind::TupleField(base, _) => {
            let (root, fields, _) = path(base)?;
            Some((root, fields, true))
        }
        _ => None,
    }
}
