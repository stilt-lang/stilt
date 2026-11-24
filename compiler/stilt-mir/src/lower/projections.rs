//! Projections (projections.call-is-place, projections.when-projection-runs and
//! projections.raising-during-access), lowered so that a projection is a
//! function that takes the caller's access as one more argument, a callback given a pointer to the
//! yielded place, as Swift's `_modify` and Hylo's subscripts are. `g.at(1, 0) = 5` calls `at` with
//! a callback that stores `5`, a read calls it with one that copies the place's words out, and
//! nested projections nest their callbacks.
//!
//! A statement or a call whose places are rooted in projections' calls is lowered in two steps, as
//! the reference interpreter prepares and opens a place (projections.when-projection-runs): first
//! every expression of it is evaluated in its turn, the projections' own arguments and the index
//! expressions of the places among them, and recorded by its node ([`Lower::evaluated`]), with a
//! pointer to the root of each place of the function's own ([`Lower::roots`]); then the projections
//! are opened one by one, the arguments of a projection before it and from left to right, each by a
//! call of the projection with a callback whose code opens the next, and the last callback lowers
//! the statement again, which now finds its values recorded and each projection's call opened as a
//! pointer ([`Lower::opened`]). A callback is a closure of the function, its environment the values
//! recorded so far, and runs in the caller's frame as the access does: its raise goes to the
//! caller, past the projection, which doesn't resume (projections.raising-during-access). A value
//! that the access gives, as a call's result or a read's copy, goes to the caller through memory it
//! provides ([`Lower::out`]).

use stilt_hir::hir::Mode;
use stilt_syntax::TextRange;
use stilt_types::tast::{self, Expr, ExprKind};
use stilt_types::ty::{Row, Ty};

use super::words::operands;
use super::{Conv, Lower};
use crate::FnRef;
use crate::mir::{Arg, Callee, Const, Heapness, Local, Operand, ParamMode, Repr, Rvalue};

/// A node of the typed body, by its address, which is stable while the body is lowered.
pub(crate) type Node = usize;

pub(crate) fn node(e: &Expr) -> Node {
    std::ptr::from_ref(e) as usize
}

/// What the code inside the last callback does, and the words it gives, which go to `out`.
type Action<'x, 'a> = &'x dyn Fn(&mut Lower<'a>) -> Vec<Operand>;

/// The projections of a statement or a call, in the order they are opened: the arguments of a
/// projection before it, and from left to right (projections.when-projection-runs).
#[derive(Default)]
pub(crate) struct Plan<'e> {
    pub(crate) projections: Vec<&'e Expr>,
}

impl Plan<'_> {
    /// Whether an argument is a place rooted in a projection's call that isn't opened yet, so
    /// that its call must open it first.
    pub(crate) fn needs(l: &Lower<'_>, args: &[tast::Arg]) -> bool {
        args.iter().any(|a| {
            a.mode == Mode::Inout && a.value.rooted_in_projection() && !l.is_open(&a.value)
        })
    }
}

impl<'a> Lower<'a> {
    /// Whether the projection's call that a place is rooted in is opened, as a pointer to its
    /// yielded place. A place with an error has nothing to open: the function can't run.
    pub(crate) fn is_open(&self, e: &Expr) -> bool {
        let mut e = e;
        loop {
            match &e.kind {
                ExprKind::Project(..) => return self.opened.contains_key(&node(e)),
                ExprKind::Error => return true,
                ExprKind::Field(base, _)
                | ExprKind::TupleField(base, _)
                | ExprKind::Index(base, _) => {
                    e = base;
                }
                _ => return false,
            }
        }
    }

    /// Lowers a construct whose places are rooted in projections' calls: `prepare` evaluates
    /// its expressions, in order, and gives its projections; `action` lowers it again inside the
    /// last callback, giving a value of type `ty`, which this returns. The recordings of an
    /// enclosing construct are kept apart.
    pub(crate) fn with_projections<'e>(
        &mut self,
        prepare: &dyn Fn(&mut Lower<'a>, &mut Plan<'e>),
        ty: &Ty,
        action: Action<'_, 'a>,
    ) -> Vec<Operand>
    where
        'a: 'e,
    {
        let outer = (
            std::mem::take(&mut self.evaluated),
            std::mem::take(&mut self.opened),
            std::mem::take(&mut self.roots),
            self.out.take(),
        );
        let mut plan = Plan::default();
        prepare(self, &mut plan);
        // The value the access gives comes back through memory of this frame.
        let temps = self.temps(ty);
        for &t in &temps {
            self.b.assign(t, Rvalue::Use(Operand::word(0)));
        }
        if !temps.is_empty() {
            self.b.make_slots(&temps);
            let pointer = self.b.define(Repr::Scalar, Rvalue::SlotOf(temps[0]));
            self.out = Some((pointer, ty.clone()));
        }
        self.open(&plan, 0, action);
        (self.evaluated, self.opened, self.roots, self.out) = outer;
        operands(&temps)
    }

    /// Opens the projections of a plan from the one at `i` on, each inside the callback of the
    /// one before, and runs `action` inside the last.
    fn open<'e>(&mut self, plan: &Plan<'e>, i: usize, action: Action<'_, 'a>)
    where
        'a: 'e,
    {
        let Some(&e) = plan.projections.get(i) else {
            let words = action(self);
            if let Some((out, ty)) = self.out.clone() {
                self.store_words(&Operand::Local(out), words, &ty);
            }
            return;
        };
        let ExprKind::Project(callee, targs, args, row) = &e.kind else {
            unreachable!("a plan holds projections' calls")
        };
        let callback = self.callback(plan, i, action);
        self.call_projection(callee, targs, args, row, e, callback);
    }

    /// Calls a projection with the callback that holds the caller's access
    /// (projections.when-projection-runs): its arguments are read when the call starts, and written
    /// back when it returns or raises, as any call's are, and the access may raise through it.
    fn call_projection(
        &mut self,
        callee: &tast::Callee,
        targs: &[Ty],
        args: &[tast::Arg],
        row: &Row,
        e: &Expr,
        callback: Operand,
    ) {
        let target = self.resolve(callee, targs);
        let forms = self.forms_of(&target);
        let (mut values, writebacks) = self.arguments(args, &forms);
        values.push(Arg::Borrow(callback));
        let loc = self.loc_at(e.at);
        self.emit_call(target, values, &writebacks, loc, true, &Ty::unit(), row);
    }

    /// The callback that opens the projections of a plan after the one at `i`, and runs
    /// `action` inside the last: a closure whose environment holds the values recorded so far,
    /// the pointers of the places opened and the memory for the value, after the witnesses and
    /// dictionaries in scope and the access of the projection being lowered, if any.
    fn callback<'e>(&mut self, plan: &Plan<'e>, i: usize, action: Action<'_, 'a>) -> Operand
    where
        'a: 'e,
    {
        let index = self.next_closure;
        self.next_closure += 1;
        let name = FnRef::Closure(Box::new(self.b.name().clone()), index);
        let mut env: Vec<(Operand, Heapness)> = vec![(
            Operand::Const(Const::Code(name.clone())),
            Heapness::Static(false),
        )];
        for (_, g) in self.generics.clone() {
            env.push((Operand::Local(g.witness), Heapness::Static(false)));
            env.extend(
                g.dicts
                    .iter()
                    .map(|(_, d)| (d.clone(), Heapness::Static(true))),
            );
            env.extend(g.desc.map(|d| (d, Heapness::Static(true))));
        }
        if let Some(access) = self.access {
            env.push((Operand::Local(access), Heapness::Static(true)));
        }
        let captured = self.captured();
        for (words, ty) in &captured.values {
            let layout = self.layout(ty);
            for (w, repr) in words.iter().zip(layout) {
                env.push((w.clone(), Heapness::of(repr)));
            }
        }
        for p in &captured.pointers {
            env.push((p.clone(), Heapness::Static(false)));
        }
        let len = env.iter().map(|(_, h)| h.words()).sum();
        let function = self.callback_function(name, &captured, len, (plan, i, action));
        self.closures.extend(function);
        self.alloc(0, env)
    }

    /// The values recorded so far, and the pointers, in the order the environment holds them.
    fn captured(&self) -> Captured {
        let mut nodes: Vec<&Node> = self.evaluated.keys().collect();
        nodes.sort_unstable();
        let values: Vec<(Vec<Operand>, Ty)> =
            nodes.iter().map(|n| self.evaluated[*n].clone()).collect();
        let mut opened: Vec<(&Node, &Local)> = self.opened.iter().collect();
        opened.sort_unstable_by_key(|(n, _)| **n);
        let mut roots: Vec<(&Node, &Local)> = self.roots.iter().collect();
        roots.sort_unstable_by_key(|(n, _)| **n);
        let mut pointers: Vec<Operand> = Vec::new();
        let mut names = Vec::new();
        for (n, p) in opened.into_iter().chain(roots) {
            names.push(*n);
            pointers.push(Operand::Local(*p));
        }
        let out = self.out.clone();
        if let Some((p, _)) = &out {
            pointers.push(Operand::Local(*p));
        }
        let opened = self.opened.len();
        Captured {
            values,
            nodes: nodes.into_iter().copied().collect(),
            pointers,
            names,
            opened,
            out: out.map(|(_, ty)| ty),
        }
    }

    /// The code of a callback: it reads its environment back, opens the projections of the plan
    /// after `i` and runs `action`, and raises what the access raises in one word, as a closure
    /// does.
    fn callback_function<'e>(
        &mut self,
        name: FnRef,
        captured: &Captured,
        len: usize,
        (plan, i, action): (&Plan<'e>, usize, Action<'_, 'a>),
    ) -> Vec<crate::mir::Function>
    where
        'a: 'e,
    {
        let mut l = Lower::new(self.cx, name, self.std);
        l.origin.clone_from(&self.origin);
        l.names.clone_from(&self.names);
        l.ret = Conv::of(Ty::unit());
        l.err = Conv::boxed(self.paired_error().unwrap_or(Ty::Error));
        l.raises_to_slot = true;
        let env = l.b.param(Repr::Heap, ParamMode::Borrowed, None);
        // The pointer to the yielded place, whose words the generics read below tell.
        let yielded = l.b.param(Repr::Scalar, ParamMode::Ref, None);
        let mut fields = Fields {
            env,
            len: u32::try_from(len).expect("under 4G captures"),
            next: 1,
        };
        for (ty, g) in &self.generics {
            let witness = fields.read(&mut l, Repr::Scalar);
            let dicts = g
                .dicts
                .iter()
                .map(|(t, _)| (t.clone(), Operand::Local(fields.read(&mut l, Repr::Heap))))
                .collect();
            l.push_generic(ty.clone(), witness, dicts, Some(&super::keys::held_of(g)));
            if g.desc.is_some() {
                let desc = Operand::Local(fields.read(&mut l, Repr::Heap));
                l.set_descriptor(ty, desc);
            }
        }
        if self.access.is_some() {
            l.access = Some(fields.read(&mut l, Repr::Heap));
        }
        fields.captured(&mut l, captured);
        let yielded_ty = &plan.projections[i].ty;
        if l.one_word(yielded_ty) {
            l.b.decl_mut(yielded).repr = l.ref_repr(yielded_ty);
        }
        l.opened.insert(node(plan.projections[i]), yielded);
        l.open(plan, i + 1, action);
        l.return_(Vec::new());
        l.finish()
    }

    /// Evaluates the arguments of a call, in order, for a plan: each `let` argument's value is
    /// recorded, and each `inout` one's place prepared.
    pub(crate) fn prepare_args<'e>(&mut self, args: &'e [tast::Arg], plan: &mut Plan<'e>) {
        for a in args {
            match a.mode {
                Mode::Let => self.record_value(&a.value),
                Mode::Inout => self.prepare_place(&a.value, plan),
            }
        }
    }

    /// Evaluates an expression and records its value by its node, unless it is recorded.
    pub(crate) fn record_value(&mut self, e: &Expr) {
        if self.evaluated.contains_key(&node(e)) {
            return;
        }
        let words = self.expr(e);
        let temps = self.copy_into_temps(words, &e.ty);
        self.evaluated
            .insert(node(e), (operands(&temps), e.ty.clone()));
    }

    /// Prepares a place: evaluates its index expressions and the arguments of the projections
    /// it is rooted in, in order, and records a pointer to the root of one rooted in a variable
    /// of this frame. A projection's call is added to the plan after its own arguments'.
    pub(crate) fn prepare_place<'e>(&mut self, e: &'e Expr, plan: &mut Plan<'e>) {
        match &e.kind {
            ExprKind::Local(_) => {
                if !self.roots.contains_key(&node(e)) {
                    let place = self.place(e);
                    let pointer = self.root_slot(&place.root);
                    let pointer = pointer.local().expect("a pointer to a root is a local");
                    self.roots.insert(node(e), pointer);
                }
            }
            ExprKind::Field(base, _) | ExprKind::TupleField(base, _) => {
                self.prepare_place(base, plan);
            }
            ExprKind::Index(base, key) => {
                self.prepare_place(base, plan);
                self.record_value(key);
            }
            ExprKind::Project(_, _, args, _) => {
                self.prepare_args(args, plan);
                plan.projections.push(e);
            }
            _ => {
                // A base that isn't a place is evaluated in its turn, as a place's parts are.
                self.record_value(e);
            }
        }
    }

    /// A read of a projection's call (projections.call-is-place): the value of the yielded place is
    /// copied out, and the projection resumes before the copy is used.
    pub(crate) fn project_read<'e>(&mut self, e: &'e Expr) -> Vec<Operand>
    where
        'a: 'e,
    {
        let ExprKind::Project(_, _, args, _) = &e.kind else {
            unreachable!("a projection's call")
        };
        let prepare = |l: &mut Lower<'a>, plan: &mut Plan<'e>| {
            l.prepare_args(args, plan);
            plan.projections.push(e);
        };
        let action = |l: &mut Lower<'a>| {
            let pointer = Operand::Local(l.opened[&node(e)]);
            l.load_words(&pointer, &e.ty)
        };
        self.with_projections(&prepare, &e.ty, &action)
    }

    /// A call whose `inout` arguments hold places rooted in projections' calls: they are opened
    /// from left to right, and the call runs inside the last (projections.when-projection-runs).
    pub(crate) fn call_through<'e>(&mut self, args: &'e [tast::Arg], e: &'e Expr) -> Vec<Operand>
    where
        'a: 'e,
    {
        let prepare = |l: &mut Lower<'a>, plan: &mut Plan<'e>| l.prepare_args(args, plan);
        let action = |l: &mut Lower<'a>| l.expr(e);
        self.with_projections(&prepare, &e.ty, &action)
    }

    /// `yield p` (projections.yield): the place is handed to the caller's access, and the body goes
    /// on once the access is done, unless it raised (projections.raising-during-access).
    pub(crate) fn yield_<'e>(&mut self, p: &'e Expr, at: TextRange)
    where
        'a: 'e,
    {
        if p.rooted_in_projection() && !self.is_open(p) {
            let prepare = |l: &mut Lower<'a>, plan: &mut Plan<'e>| l.prepare_place(p, plan);
            let action = |l: &mut Lower<'a>| {
                l.yield_(p, at);
                Vec::new()
            };
            self.with_projections(&prepare, &Ty::unit(), &action);
            return;
        }
        let (pointer, writeback) = if is_place(p) || p.rooted_in_projection() {
            let place = self.place(p);
            self.inout(place)
        } else {
            // A view that no place holds is bound to a temporary of the statement.
            let words = self.expr(p);
            let temps = self.copy_into_temps(words, &p.ty);
            self.b.make_slots(&temps);
            let pointer = self.b.define_op(Repr::Scalar, Rvalue::SlotOf(temps[0]));
            (pointer, None)
        };
        let access = self.access.expect("a yield is in a projection's body");
        // The access raises in one word, or to the memory this function was given for an
        // error of several words, and the error goes to the caller as it came: no `catch` of the
        // projection's own is around a `yield` (projections.once-on-every-path), so none sees it
        // (projections.raising-during-access).
        let mut args = vec![Arg::Ref(pointer)];
        let err = Conv::boxed(Ty::Error);
        let raised = self.slot_for_error(&mut args, &err, true);
        let loc = self.loc_at(at);
        let callee = Callee::Value(Operand::Local(access));
        let writebacks: Vec<_> = writeback.into_iter().collect();
        self.call_raising(
            callee,
            args,
            &writebacks,
            loc,
            &Conv::of(Ty::unit()),
            raised,
        );
    }
}

/// Whether an expression names a place of this frame: a variable, or a field, an element or an
/// index of one (expressions.places).
fn is_place(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Local(_) => true,
        ExprKind::Field(base, _) | ExprKind::TupleField(base, _) | ExprKind::Index(base, _) => {
            is_place(base)
        }
        _ => false,
    }
}

/// What a callback's environment holds beyond the generics and the access: the values recorded,
/// by their nodes, then the pointers of the places opened, `opened` of them, and of the roots,
/// by their nodes, then the memory for the value given, of this type.
struct Captured {
    values: Vec<(Vec<Operand>, Ty)>,
    nodes: Vec<Node>,
    pointers: Vec<Operand>,
    names: Vec<Node>,
    opened: usize,
    out: Option<Ty>,
}

/// The fields of a callback's environment, read back in order into borrowed locals.
struct Fields {
    env: Local,
    len: u32,
    next: u32,
}

impl Fields {
    fn read(&mut self, l: &mut Lower<'_>, repr: Repr) -> Local {
        let local = l.borrowed_field(self.env, self.len, self.next, repr);
        self.next += u32::try_from(repr.words()).expect("under 4G words");
        local
    }

    /// Reads what was captured into the callback's recordings.
    fn captured(&mut self, l: &mut Lower<'_>, captured: &Captured) {
        for (n, (_, ty)) in captured.nodes.iter().zip(&captured.values) {
            let words = l
                .layout(ty)
                .into_iter()
                .map(|repr| Operand::Local(self.read(l, repr)))
                .collect();
            l.evaluated.insert(*n, (words, ty.clone()));
        }
        for (k, n) in captured.names.iter().enumerate() {
            let pointer = self.read(l, Repr::Scalar);
            if k < captured.opened {
                l.opened.insert(*n, pointer);
            } else {
                l.roots.insert(*n, pointer);
            }
        }
        if let Some(ty) = &captured.out {
            let pointer = self.read(l, Repr::Scalar);
            l.out = Some((pointer, ty.clone()));
        }
    }
}
