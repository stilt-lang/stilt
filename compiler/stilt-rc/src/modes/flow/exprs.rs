//! The walk of a body's statements and expressions in source order, each with where its value goes.
//! Rule numbers in comments refer to the Reference's chapter on modes, unless they name another
//! record.

mod branches;
mod calls;
mod steps;

use stilt_hir::hir::{LocalId, Name};
use stilt_syntax::{TextRange, TextSize};
use stilt_types::tast::walk::{self, Part};
use stilt_types::tast::{Binding, Block, Code, Expr, ExprKind, Stmt, StmtKind};

use super::places::{self, Step, binders, indexes, pattern_parts};
use super::{
    Assigned, Calls, Copy, Decl, END, Flow, Holder, How, Into, Kind, Modification, Stored, Tick,
    Write,
};

/// A place of a binding passed to a parameter that a call consumes or may store, which the call
/// copies, or whose copies it passes on: the binding, the path, where it is and its tick, and what
/// holds the call's result.
type Passed = (LocalId, Vec<Step>, Made, Holder);

/// Where a copy is made, and the tick there.
type Made = (TextSize, Tick);

/// A loop around the code walked: its head, and its `break`s and `continue`s so far.
struct Target {
    head: Tick,
    breaks: Vec<Tick>,
    continues: Vec<Tick>,
}

pub(super) struct Walk<'a> {
    calls: &'a dyn Calls,
    names: &'a [Name],
    /// The function, 0, or the closure literal being walked.
    frame: u32,
    frames: u32,
    /// The loops of the frame around the code being walked, innermost last.
    targets: Vec<Target>,
    passed: Vec<Passed>,
    pub(super) flow: Flow,
}

impl<'a> Walk<'a> {
    pub(super) fn new(calls: &'a dyn Calls, names: &'a [Name]) -> Self {
        let mut flow = Flow::default();
        flow.paths.at.push(TextSize::new(0));
        Self {
            calls,
            names,
            frame: 0,
            frames: 0,
            targets: Vec::new(),
            passed: Vec::new(),
            flow,
        }
    }

    pub(super) fn declare(&mut self, v: LocalId, kind: Kind, scope: TextRange) {
        let frame = self.frame;
        self.flow.decls.insert(v, Decl { kind, frame, scope });
    }

    /// A body's code, whose value its function returns.
    pub(super) fn code(&mut self, code: &Code) {
        let returned = Into::leaving(How::Returned);
        match code {
            Code::Block(b) => self.block(b, &returned),
            Code::Expr(e) => self.expr(e, &returned),
        }
    }

    /// A copy, `stored` in a value, captured or kept in a call's result rather than bound by a
    /// pattern itself, at the place `at` inside its holder's value if it has one.
    fn copy(
        &mut self,
        binding: LocalId,
        path: Vec<Step>,
        (at_came, made): Made,
        holder: Holder,
        stored: bool,
        at: Option<Vec<Step>>,
    ) {
        self.flow.copies.push(Copy {
            binding,
            path,
            at_came,
            made,
            came: made,
            holder,
            stored,
            at,
            wide: false,
        });
    }

    /// A modification of a place, where `at` is, at a tick at `ends`.
    fn write(&mut self, place: &Expr, at: TextRange, ends: TextSize, replaces: bool) {
        if let Some((binding, path)) = places::place(place) {
            let tick = self.tick(ends);
            self.flow.writes.push(Write {
                binding,
                path,
                at,
                tick,
                replaces,
                how: Modification::Write,
            });
        }
    }

    /// The binding a place of this frame is part of, if its declaration is known.
    fn own(&self, v: LocalId) -> Option<Decl> {
        self.flow
            .decls
            .get(&v)
            .copied()
            .filter(|d| d.frame == self.frame)
    }

    pub(super) fn block(&mut self, b: &Block, into: &Into<'_>) {
        let end = scope(b, TextSize::new(0));
        for (i, s) in b.iter().enumerate() {
            match &s.kind {
                StmtKind::Expr(x) if i + 1 == b.len() => self.expr(x, into),
                StmtKind::Expr(x) | StmtKind::Assert(x) => self.expr(x, &Into::read(s.at.end())),
                StmtKind::Let(binding) => self.binding(s, binding, Kind::Let, end),
                StmtKind::Var(binding) => self.binding(s, binding, Kind::Var, end),
                StmtKind::Assign(op, place, value) => self.assign(s, op.is_some(), place, value),
                StmtKind::Yield(place) => self.yield_(s, place),
            }
        }
    }

    /// A `yield` hands its place to the caller, who may modify it: yielding a binding is where it
    /// escapes (projections.yield; projections.once-on-every-path), and modifies it
    /// (projections.nested). A view that no place holds is yielded from a temporary.
    fn yield_(&mut self, s: &Stmt, place: &Expr) {
        for x in indexes(place) {
            self.expr(x, &Into::read(s.at.end()));
        }
        let into = Into {
            leaves: Some(How::Yielded),
            ..Into::read(END)
        };
        self.expr(place, &into);
        self.write(place, s.at, s.at.end(), false);
    }

    /// A `let` or `var` statement: its value is bound by its pattern, whose bindings last
    /// for `end`, their block, and start anew where the statement runs again
    /// (modes.shared-writes).
    fn binding(&mut self, s: &Stmt, b: &Binding, kind: Kind, end: TextRange) {
        let bound = binders(&b.pattern);
        self.bind_at(&bound, s.at.start());
        let into = Into {
            held: Some(Holder::Bound(bound.clone(), end)),
            pattern: Some(&b.pattern),
            ..Into::read(s.at.end())
        };
        self.expr(&b.value, &into);
        if let Some(otherwise) = &b.otherwise {
            self.expr(otherwise, &Into::read(s.at.end()));
        }
        for v in bound {
            self.declare(v, kind, end);
        }
    }

    /// An assignment to the whole of a local copies its value, held by the local until its
    /// scope ends (modes.copies); one to an `inout` parameter, to a part of a binding or through an
    /// index stores it in that binding (modes.escaping). Neither stores the value in its own
    /// binding. A compound assignment only reads it. Assigning a whole binding replaces its value,
    /// and every other assignment modifies it (modes.shared-writes).
    fn assign(&mut self, s: &Stmt, compound: bool, place: &Expr, value: &Expr) {
        for x in indexes(place) {
            self.expr(x, &Into::read(s.at.end()));
        }
        let target = places::place(place);
        let read = Into::read(s.at.end());
        let into = match &target {
            Some((root, path)) if !compound => match self.flow.decls.get(root) {
                Some(d) if path.is_empty() && !matches!(d.kind, Kind::Param(_)) => Into {
                    held: Some(Holder::Bound(vec![*root], d.scope)),
                    ..read
                },
                _ => Into {
                    leaves: Some(How::Assigned(self.names[root.0 as usize])),
                    held: Some(Holder::Place(*root)),
                    at: Some(path.clone()),
                    ..read
                },
            },
            _ => read,
        };
        let start = self.tick(s.at.start());
        self.expr(value, &into);
        match target {
            Some((binding, path)) if !compound => {
                let modifies = !path.is_empty();
                let tick = self.tick(s.at.end());
                self.flow.assigned.push(Assigned {
                    binding,
                    path,
                    start,
                    tick,
                });
                if modifies {
                    self.write(place, s.at, s.at.end(), true);
                }
            }
            _ => self.write(place, s.at, s.at.end(), false),
        }
    }

    fn expr(&mut self, e: &Expr, into: &Into<'_>) {
        if let Some((root, path)) = places::place(e) {
            return self.place(e, root, path, into);
        }
        let read = Into::read(e.at.end());
        match &e.kind {
            ExprKind::Record(item, _, fields) => {
                let stored = Stored::Record(item.name);
                let fields = fields.iter().map(|(n, x)| (Some(Step::Field(*n)), x));
                self.literal(fields, &stored, into);
            }
            ExprKind::Construct(item, _, args) => {
                let args = args.iter().map(|x| (None, x));
                self.literal(args, &Stored::Variant(item.name), into);
            }
            ExprKind::Tuple(xs) => {
                let xs = xs.iter().enumerate();
                let xs = xs.map(|(i, x)| (Some(Step::Field(i.to_string().into())), x));
                self.literal(xs, &Stored::Tuple, into);
            }
            ExprKind::List(xs) => {
                let xs = xs.iter().map(|x| (Some(Step::Index), x));
                self.literal(xs, &Stored::List, into);
            }
            // Each value a spread's body gives is an element of what holds the spread
            // (variadics.spread-expressions).
            ExprKind::Spread(s) => self.again(e.at, |w| w.expr(&s.body, into)),
            ExprKind::Closure(params, body) => self.closure(e, params, body, into),
            ExprKind::Call(callee, _, args, _) | ExprKind::Project(callee, _, args, _) => {
                self.call(e, callee, args, into);
            }
            ExprKind::CallValue(f, args) => {
                self.expr(f, &read);
                self.args(e, args, &[], None, into);
            }
            _ => self.control(e, into),
        }
    }

    pub(super) fn parts(&mut self, e: &Expr, into: &Into<'_>) {
        for part in walk::parts(e) {
            match part {
                Part::Expr(x) => self.expr(x, into),
                Part::Block(b) => self.block(b, into),
            }
        }
    }

    /// A place whose value goes where `into` says: a binding of this frame with a value of a
    /// copy-on-write type escapes, is copied, or is passed to a call that may lose its reuse. A
    /// part of a binding's own value that goes back into the binding, directly or through a call
    /// whose result it holds, is no copy, but the binding's copies made before carry over to it
    /// (modes.shared-self-parts). A captured binding of
    /// an enclosing frame is copied too, so that its copies count where it is read when the
    /// closure ends.
    fn place(&mut self, e: &Expr, root: LocalId, path: Vec<Step>, into: &Into<'_>) {
        for x in indexes(e) {
            self.expr(x, &Into::read(into.lasts));
        }
        let read = self.tick(e.at.start());
        self.flow.reads.push((root, read));
        let into_itself = into
            .held
            .iter()
            .chain(&into.result)
            .any(|h| h.bindings().contains(&root));
        if !self.calls.cow(&e.ty) {
            return;
        }
        let at = e.at.start();
        let made = (at, self.tick(at));
        let Some(decl) = self.own(root) else {
            if !into_itself && self.flow.decls.contains_key(&root) {
                self.copies(root, &path, made, into);
            }
            return;
        };
        let through_call = into.held.is_none();
        if let Some(how) = &into.leaves
            && (through_call || !into_itself)
            && !matches!(decl.kind, Kind::Param(_))
        {
            self.flow.escapes.push((root, at, how.clone()));
        }
        if into_itself {
            self.flow.selves.push((root, path, into.at.clone(), made.1));
            return;
        }
        self.copies(root, &path, made, into);
        if let Some(result) = &into.result {
            self.passed.push((root, path, made, result.clone()));
        }
    }

    /// The copies of a part of a binding that a value going where `into` says makes
    /// (modes.copies).
    fn copies(&mut self, root: LocalId, path: &[Step], at: Made, into: &Into<'_>) {
        match (&into.held, into.pattern) {
            (Some(Holder::Bound(_, end)), Some(pattern)) => {
                let mut parts = Vec::new();
                pattern_parts(pattern, path, &mut parts);
                for (part, v, ty) in parts {
                    if self.calls.cow(&ty) {
                        let holder = Holder::Bound(vec![v], *end);
                        self.copy(root, part, at, holder, false, Some(Vec::new()));
                    }
                }
            }
            (Some(holder), _) => {
                let stored = into.leaves.is_some();
                let (holder, at_place) = (holder.clone(), into.at.clone());
                self.copy(root, path.to_vec(), at, holder, stored, at_place);
            }
            (None, _) => {}
        }
    }

    /// A literal stores each of its elements in a value that what holds the literal holds, at the
    /// element's place inside it if it has one.
    fn literal<'e>(
        &mut self,
        elements: impl IntoIterator<Item = (Option<Step>, &'e Expr)>,
        stored: &Stored,
        into: &Into<'_>,
    ) {
        for (step, x) in elements {
            let at = into.at.as_ref().zip(step).map(|(at, step)| {
                let mut at = at.clone();
                at.push(step);
                at
            });
            let inner = Into {
                leaves: Some(How::Stored(stored.clone())),
                held: Some(into.keeper()),
                at,
                ..Into::read(into.lasts)
            };
            self.expr(x, &inner);
        }
    }
}

/// The scope of the bindings of a block: from its first statement to the end of its last, or
/// `at` when it has none.
fn scope(b: &Block, at: TextSize) -> TextRange {
    match (b.first(), b.last()) {
        (Some(first), Some(last)) => TextRange::new(first.at.start(), last.at.end()),
        _ => TextRange::empty(at),
    }
}
