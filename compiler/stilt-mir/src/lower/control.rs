//! Expressions that decide what runs next: blocks, branches, loops, jumps, and raises
//! (expressions.if, expressions.match and expressions.loops; effects.raise). A branch's value joins
//! in locals of its type's layout.

use stilt_types::tast::{Arm, Block, Catch, Expr, ExprKind, Iterable, Pat, Stmt, StmtKind};
use stilt_types::ty::Ty;

use super::words::{operands, word};
use super::{Catcher, Loop, Lower};
use crate::mir::{
    BlockId, Counted, Local, NumKind, Operand, Prim, Repr, Runtime, Rvalue, Terminator,
};
use crate::repr::num_kind;

impl Lower<'_> {
    pub(crate) fn control(&mut self, e: &Expr) -> Vec<Operand> {
        match &e.kind {
            ExprKind::Block(b) => self.block(b),
            ExprKind::If(c, then, otherwise) => self.if_(c, then, otherwise.as_deref(), e),
            ExprKind::IfLet(p, x, then, otherwise) => {
                self.if_let(p, x, then, otherwise.as_deref(), e)
            }
            ExprKind::Match(x, arms) => {
                let v = self.expr(x);
                self.arms(arms, &v, &e.ty)
            }
            ExprKind::Loop(..) | ExprKind::While(..) | ExprKind::For(..) => self.counted_loop(e),
            ExprKind::Else(a, b) => self.else_(a, b, &e.ty),
            ExprKind::Try(x, None) => self.expr(x),
            ExprKind::Try(x, Some(c)) => self.try_catch(x, c, &e.ty),
            ExprKind::Raise(x) => {
                let error = self.expr(x);
                self.raise(error);
                vec![Operand::word(0)]
            }
            ExprKind::Return(x) => {
                let v = x
                    .as_ref()
                    .map_or_else(|| vec![Operand::word(0)], |x| self.expr(x));
                self.return_(v);
                vec![Operand::word(0)]
            }
            ExprKind::Break | ExprKind::Continue => {
                let l = *self.loops.last().expect("a jump inside a loop");
                self.leave_withs(l.withs);
                let to = if matches!(e.kind, ExprKind::Break) {
                    l.exit
                } else {
                    l.next
                };
                self.b.goto(to);
                vec![Operand::word(0)]
            }
            ExprKind::Closure(params, body) => vec![self.closure(params, body, e)],
            ExprKind::Handler(h) => vec![self.handler_lit(h)],
            ExprKind::With(h, effect, _, b) => self.with_(h, effect, b, &e.ty),
            ExprKind::Resume(v) => self.resume_(v.as_deref(), e),
            ExprKind::When(held, b) => self.when_(held, b, e),
            _ => unreachable!("not an expression of control: {:?}", e.kind),
        }
    }

    /// Returns the words of the function's result, in its convention, leaving the `with`s it
    /// is inside.
    pub(crate) fn return_(&mut self, words: Vec<Operand>) {
        self.leave_withs(0);
        let ret = self.ret.clone();
        let words = self.passed(words, &ret);
        self.b.terminate(Terminator::Return(words));
    }

    /// Raises an error: to the innermost `catch`, or out of the function, in its convention.
    pub(crate) fn raise(&mut self, error: Vec<Operand>) {
        if let Some(c) = self.catchers.last().cloned() {
            for (i, &l) in c.error.iter().enumerate() {
                self.b.assign(l, Rvalue::Use(word(&error, i)));
            }
            self.b.goto(c.arms);
        } else {
            self.raise_out(error);
        }
    }

    /// The statements of a block, and its value: that of its last statement if it is an
    /// expression, and `()` otherwise.
    pub(crate) fn block(&mut self, b: &Block) -> Vec<Operand> {
        let Some((last, rest)) = b.split_last() else {
            return vec![Operand::word(0)];
        };
        for s in rest {
            self.stmt(s);
        }
        if let StmtKind::Expr(e) = &last.kind {
            self.source_at(last.at);
            self.expr(e)
        } else {
            self.stmt(last);
            vec![Operand::word(0)]
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        self.source_at(s.at);
        match &s.kind {
            StmtKind::Let(b) | StmtKind::Var(b) => {
                let v = self.expr(&b.value);
                // The binding belongs to the statement, not to the last line of its value.
                self.source_at(s.at);
                let mutable = matches!(s.kind, StmtKind::Var(_));
                self.binding(&b.pattern, v, mutable, b.otherwise.as_deref());
            }
            // A place rooted in a projection's call opens the projection first
            // (projections.when-projection-runs; `projections`).
            StmtKind::Assign(op, place, value)
                if place.rooted_in_projection() && !self.is_open(place) =>
            {
                let (op, at) = (*op, s.at);
                let prepare = |l: &mut Lower<'_>, plan: &mut _| {
                    l.prepare_place(place, plan);
                    l.record_value(value);
                };
                let action = |l: &mut Lower<'_>| {
                    l.assign(op, place, value, at);
                    Vec::new()
                };
                self.with_projections(&prepare, &Ty::unit(), &action);
            }
            StmtKind::Assign(op, place, value) => self.assign(*op, place, value, s.at),
            StmtKind::Assert(c) => {
                let loc = self.loc_at(s.at);
                if let Some(compared) = self.compared(c) {
                    return self.assert_compared(&compared, loc);
                }
                let v = self.expr1(c);
                let (ok, failed) = (self.b.new_block(), self.b.new_block());
                self.b.branch(v, ok, failed);
                self.b.switch_to(failed);
                self.panic(6, None, loc);
                self.b.switch_to(ok);
            }
            StmtKind::Expr(e) => {
                self.expr(e);
            }
            StmtKind::Yield(p) => self.yield_(p, s.at),
        }
    }

    /// Assigns the words of a value to the locals `result`, then jumps to `join`.
    pub(crate) fn into(&mut self, result: &[Local], value: &[Operand], join: BlockId) {
        for (i, &l) in result.iter().enumerate() {
            self.b.assign(l, Rvalue::Use(word(value, i)));
        }
        self.b.goto(join);
    }

    /// A loop, whose place a profile counts each run of its body at (builds.profiles).
    fn counted_loop(&mut self, e: &Expr) -> Vec<Operand> {
        self.loop_places.push(e.at);
        let v = match &e.kind {
            ExprKind::Loop(b) => self.loop_(b),
            ExprKind::While(c, b) => self.while_(c, b),
            ExprKind::For(p, iterable, b) => self.for_(p, iterable, b),
            _ => unreachable!("a loop"),
        };
        self.loop_places.pop();
        v
    }

    /// `if c { … } else …`: a profile counts its first arm at the condition's place, and its
    /// other at the `else`'s, or at the `if`'s when it has none (builds.profiles).
    fn if_(&mut self, c: &Expr, then: &Block, otherwise: Option<&Expr>, e: &Expr) -> Vec<Operand> {
        let ty = &e.ty;
        // A bound test gives the branch it guards the dictionaries it finds (meta.bound-tests).
        let (cond, guard) = match &c.kind {
            ExprKind::Bound(t, traits) => {
                let (cond, dicts) = self.bound_test(t, traits);
                (cond, Some((t.clone(), dicts)))
            }
            _ => (self.expr1(c), None),
        };
        let result = self.temps(ty);
        let (yes, no, join) = (self.b.new_block(), self.b.new_block(), self.b.new_block());
        self.b.branch(cond, yes, no);
        self.b.switch_to(yes);
        self.count_at(Counted::Arm, c.at);
        let v = match guard {
            Some((t, dicts)) => self.guarded(&t, dicts, then),
            None => self.block(then),
        };
        self.into(&result, &v, join);
        self.b.switch_to(no);
        self.count_at(Counted::Arm, otherwise.map_or(e.at, |x| x.at));
        let v = otherwise.map_or_else(|| vec![Operand::word(0)], |x| self.expr(x));
        self.into(&result, &v, join);
        self.b.switch_to(join);
        operands(&result)
    }

    /// `if let P = e { … }`: the value of `e` matched as an arm without a guard, then the first
    /// block or the `else` (expressions.if-let).
    fn if_let(
        &mut self,
        p: &Pat,
        x: &Expr,
        then: &Block,
        otherwise: Option<&Expr>,
        e: &Expr,
    ) -> Vec<Operand> {
        let ty = &e.ty;
        let v = self.expr(x);
        let result = self.temps(ty);
        let (yes, no, join) = (self.b.new_block(), self.b.new_block(), self.b.new_block());
        let mark = self.generics.len();
        self.matches(p, v, false, &mut |l, _| l.b.goto(yes), no);
        self.b.switch_to(yes);
        self.count_at(Counted::Arm, p.at);
        let value = self.block(then);
        self.into(&result, &value, join);
        self.close_fresh(mark);
        self.b.switch_to(no);
        self.count_at(Counted::Arm, otherwise.map_or(e.at, |x| x.at));
        let value = otherwise.map_or_else(|| vec![Operand::word(0)], |x| self.expr(x));
        self.into(&result, &value, join);
        self.b.switch_to(join);
        operands(&result)
    }

    /// The arms of a `match` or a `catch`, tried in order (patterns.match). They are exhaustive, so
    /// running out of arms can't happen.
    pub(crate) fn arms(&mut self, arms: &[Arm], v: &[Operand], ty: &Ty) -> Vec<Operand> {
        let result = self.temps(ty);
        let join = self.b.new_block();
        for arm in arms {
            let (body, next) = (self.b.new_block(), self.b.new_block());
            let mark = self.generics.len();
            self.arm_test(arm, v, body, next);
            self.b.switch_to(body);
            self.count_at(Counted::Arm, arm.pattern.at);
            let value = self.expr(&arm.body);
            self.into(&result, &value, join);
            // The fresh types of a shape's case are the arm's own (meta.fresh-types).
            self.close_fresh(mark);
            self.b.switch_to(next);
        }
        self.b.terminate(Terminator::Unreachable);
        self.b.switch_to(join);
        operands(&result)
    }

    /// `e₁ else e₂`: the value of a `Some`, or `e₂` (expressions.option-fallback).
    fn else_(&mut self, a: &Expr, b: &Expr, ty: &Ty) -> Vec<Operand> {
        let option = self.expr(a);
        let result = self.temps(ty);
        let (some, none, join) = (self.b.new_block(), self.b.new_block(), self.b.new_block());
        let is_some = self.is_variant(&option, &a.ty, 1);
        self.b.branch(is_some, some, none);
        self.b.switch_to(some);
        let fields = self.fields_of(&a.ty, 1);
        let value = self.field_words(&option, &fields, 0);
        self.into(&result, &value, join);
        self.b.switch_to(none);
        let value = self.expr(b);
        self.into(&result, &value, join);
        self.b.switch_to(join);
        operands(&result)
    }

    /// `try e catch arms`: a raise in `e` goes to the arms, with the error (effects.catch).
    fn try_catch(&mut self, x: &Expr, c: &Catch, ty: &Ty) -> Vec<Operand> {
        let error = self.temps(&c.error);
        let (arms, join) = (self.b.new_block(), self.b.new_block());
        let result = self.temps(ty);
        self.catchers.push(Catcher {
            ty: c.error.clone(),
            error: error.clone(),
            arms,
        });
        let v = self.expr(x);
        self.catchers.pop();
        self.into(&result, &v, join);
        self.b.switch_to(arms);
        self.pass_aborts();
        let v = self.arms(&c.arms, &operands(&error), ty);
        self.into(&result, &v, join);
        self.b.switch_to(join);
        operands(&result)
    }

    /// Runs a loop body, with `break` going to `exit` and `continue` to `next`.
    pub(crate) fn loop_body(&mut self, b: &Block, exit: BlockId, next: BlockId) {
        let withs = self.withs.len();
        self.loops.push(Loop { exit, next, withs });
        if let Some(&at) = self.loop_places.last() {
            self.count_at(Counted::Loop, at);
        }
        self.block(b);
        self.loops.pop();
        self.b.goto(next);
    }

    fn loop_(&mut self, b: &Block) -> Vec<Operand> {
        let (head, exit) = (self.b.new_block(), self.b.new_block());
        self.b.goto(head);
        self.b.switch_to(head);
        self.loop_body(b, exit, head);
        self.b.switch_to(exit);
        vec![Operand::word(0)]
    }

    /// The head of a `while` is outside its body, so a `break` there leaves an enclosing loop
    /// (expressions.break-and-continue).
    fn while_(&mut self, c: &Expr, b: &Block) -> Vec<Operand> {
        let (head, body, exit) = (self.b.new_block(), self.b.new_block(), self.b.new_block());
        self.b.goto(head);
        self.b.switch_to(head);
        let cond = self.expr1(c);
        self.b.branch(cond, body, exit);
        self.b.switch_to(body);
        self.loop_body(b, exit, head);
        self.b.switch_to(exit);
        vec![Operand::word(0)]
    }

    fn for_(&mut self, p: &Pat, iterable: &Iterable, b: &Block) -> Vec<Operand> {
        match iterable {
            Iterable::Iter(source) if source.ty.is_prelude("Map") => self.for_map(p, source, b),
            // A type's fields and variants (meta.fields and meta.variant-cases).
            Iterable::Iter(source)
                if source
                    .ty
                    .meta_of("Fields")
                    .or_else(|| source.ty.meta_of("Cases"))
                    .is_some() =>
            {
                self.for_reflected(p, source, b);
            }
            Iterable::Iter(source) if source.ty.arrayed().is_some() => {
                self.for_array(p, source, b);
            }
            Iterable::Iter(source) if source.ty.viewed().is_some() => self.for_view(p, source, b),
            Iterable::Iter(source) if source.ty.iterated().is_some() => {
                self.for_iter(p, source, b);
            }
            Iterable::Iter(source) => match super::pairs::pairs(p, source) {
                Some(pairs) => self.for_pairs(p, &pairs, b),
                None => self.for_list(p, source, b),
            },
            Iterable::Range(first, last, inclusive) => {
                self.for_range(p, first, last, *inclusive, b);
            }
        }
        vec![Operand::word(0)]
    }

    /// The blocks of a loop: its head, its body, the step to the next iteration, and its exit.
    pub(crate) fn loop_blocks(&mut self) -> (BlockId, BlockId, BlockId, BlockId) {
        (
            self.b.new_block(),
            self.b.new_block(),
            self.b.new_block(),
            self.b.new_block(),
        )
    }

    /// Each element of the list, as it was when the loop started (expressions.for-iterables).
    fn for_list(&mut self, p: &Pat, source: &Expr, b: &Block) {
        let list = self.expr1(source);
        let list = self.b.define_op(Repr::Heap, Rvalue::Use(list));
        let len = self.b.define_op(
            Repr::Scalar,
            Rvalue::Runtime(Runtime::ListLen, vec![list.clone()]),
        );
        let i = self.b.temp(Repr::Scalar);
        self.b.assign(i, Rvalue::Use(Operand::word(0)));
        let (head, body, next, exit) = self.loop_blocks();
        self.b.goto(head);
        self.b.switch_to(head);
        let more = self.lt(NumKind::I64, Operand::Local(i), len);
        self.b.branch(more, body, exit);
        self.b.switch_to(body);
        let at = self.loc_at(source.at);
        let x = self.list_element(list, Operand::Local(i), at, &p.ty);
        self.binding(p, x, false, None);
        self.loop_body(b, exit, next);
        self.b.switch_to(next);
        self.step(i);
        self.b.goto(head);
        self.b.switch_to(exit);
    }

    /// The entries of the map, as `(K, V)` pairs in insertion order (expressions.for-iterables). A
    /// pair holds its key and value each in the one word the map holds it in.
    fn for_map(&mut self, p: &Pat, source: &Expr, b: &Block) {
        let map = self.expr1(source);
        let map = self.b.define_op(Repr::Heap, Rvalue::Use(map));
        let position = self.b.temp(Repr::Scalar);
        self.b.assign(position, Rvalue::Use(Operand::word(0)));
        let (head, body, next, exit) = self.loop_blocks();
        self.b.goto(head);
        self.b.switch_to(head);
        let found = Rvalue::Runtime(
            Runtime::MapNext,
            vec![map.clone(), Operand::Local(position)],
        );
        self.b.assign(position, found);
        let done = self.word_eq(Operand::Local(position), Operand::word(u64::MAX));
        self.b.branch(done, exit, body);
        self.b.switch_to(body);
        let (kty, vty) = match &p.ty {
            Ty::Tuple(ts) if ts.len() == 2 => (ts[0].clone(), ts[1].clone()),
            _ => (Ty::Error, Ty::Error),
        };
        let at = |rt| Rvalue::Runtime(rt, vec![map.clone(), Operand::Local(position)]);
        let k = self.b.define_op(Repr::Scalar, at(Runtime::MapKeyAt));
        let v = self.b.define_op(Repr::Scalar, at(Runtime::MapValueAt));
        let mut words = self.map_words(&map, &k, &kty, false);
        words.extend(self.map_words(&map, &v, &vty, true));
        self.binding(p, words, false, None);
        self.loop_body(b, exit, next);
        self.b.switch_to(next);
        self.step(position);
        self.b.goto(head);
        self.b.switch_to(exit);
    }

    /// `a..b` and `a..=b`: both bounds are evaluated once, `a` first, and the loop stops at the
    /// last value without stepping past it, which may be the type's maximum
    /// (expressions.range-iteration).
    fn for_range(&mut self, p: &Pat, first: &Expr, last: &Expr, inclusive: bool, b: &Block) {
        let kind = num_kind(&p.ty).unwrap_or(NumKind::I64);
        let start = self.expr1(first);
        let end = self.expr1(last);
        let end = self.b.define_op(Repr::Scalar, Rvalue::Use(end));
        let i = self.b.temp(Repr::Scalar);
        self.b.assign(i, Rvalue::Use(start));
        let (head, body, next, exit) = self.loop_blocks();
        self.b.goto(head);
        self.b.switch_to(head);
        let go = if inclusive {
            self.le(kind, Operand::Local(i), end.clone())
        } else {
            self.lt(kind, Operand::Local(i), end.clone())
        };
        self.b.branch(go, body, exit);
        self.b.switch_to(body);
        self.binding(p, vec![Operand::Local(i)], false, None);
        self.loop_body(b, exit, next);
        self.b.switch_to(next);
        let below = self.lt(kind, Operand::Local(i), end);
        let step = self.b.new_block();
        self.b.branch(below, step, exit);
        self.b.switch_to(step);
        let one = Operand::word(1);
        self.b.assign(
            i,
            Rvalue::Prim(
                Prim::AddWrap(kind),
                vec![Operand::Local(i), one],
                Operand::word(0),
            ),
        );
        self.b.goto(head);
        self.b.switch_to(exit);
    }

    pub(crate) fn step(&mut self, i: Local) {
        let rvalue = Rvalue::Prim(
            Prim::AddWrap(NumKind::I64),
            vec![Operand::Local(i), Operand::word(1)],
            Operand::word(0),
        );
        self.b.assign(i, rvalue);
    }

    pub(crate) fn lt(&mut self, kind: NumKind, a: Operand, b: Operand) -> Operand {
        self.b.define_op(
            Repr::Scalar,
            Rvalue::Prim(Prim::Lt(kind), vec![a, b], Operand::word(0)),
        )
    }

    pub(crate) fn le(&mut self, kind: NumKind, a: Operand, b: Operand) -> Operand {
        self.b.define_op(
            Repr::Scalar,
            Rvalue::Prim(Prim::Le(kind), vec![a, b], Operand::word(0)),
        )
    }
}
