//! Handlers, `with`, `resume` and performances (handlers.handler-literals, handlers.with and
//! handlers.resuming), on the runtime's handlers (`stilt_runtime`'s `effects`).
//!
//! A handler is a data object: its kind, 0 for one that resumes at once, 1 for one that takes
//! control and never resumes, and 2 for one whose bodies resume, then for each operation the
//! hash of its name and a closure whose code takes the box of the arguments' words and gives
//! its result in one word. A `with` installs it, and removes it however its block ends: at the
//! block's end, where a handler that takes control gives the block's value to the bodies that
//! wait for it; at a `return`, `break` or `continue` out of the block; and at a raise, which a
//! `catch` around the block receives, in the error's type around the `with`, before passing it
//! on.
//!
//! A body that takes control and ends without resuming ends its `with` with its value, as an
//! *abort* that the performance raises: every row that holds an effect can raise, `async`'s
//! too, whose `await` stops so code the sequential run never reaches (`super::calls::aborts`),
//! every `catch` passes an abort on, and the `with` whose handler the abort ends takes the
//! value. A performance, `resume` and the end of a `with` are
//! calls of closures of the runtime, which can raise.

use stilt_hir::hir::{Item, Name};
use stilt_types::tast::{self, Block, Expr, ExprKind, HandlerExpr};
use stilt_types::ty::{Row, Ty};

use super::calls::error_type;
use super::words::operands;
use super::{Catcher, Conv, Exit, Lower};

use crate::mir::{Arg, BOX, Callee, Effects, Heapness, Local, Operand, Repr, Runtime, Stmt};

/// The runtime's closures, by the argument of [`Runtime::Effects(Effects::Code)`].
const PERFORM: u64 = 0;
const RESUME: u64 = 1;
const FINISH: u64 = 2;

/// A hash of a name, which the runtime finds an effect's handler and an operation by.
fn hash(name: &str) -> u64 {
    name.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| {
        (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
    })
}

fn effect_id(effect: &Item) -> u64 {
    hash(&format!("{}.{}", effect.home, effect.name))
}

/// Whether an operation's body resumes.
fn resumes(op: &Expr) -> bool {
    let mut found = false;
    tast::walk::iter(op, &mut |_| {}, &mut |e| {
        found |= matches!(e.kind, ExprKind::Resume(_));
    });
    found
}

impl Lower<'_> {
    /// A handler literal: its kind, then each operation's name and closure
    /// (handlers.handler-literals).
    pub(crate) fn handler_lit(&mut self, h: &HandlerExpr) -> Operand {
        let kind = match (h.control, h.ops.iter().any(|(_, op)| resumes(op))) {
            (false, _) => 0,
            (true, false) => 1,
            (true, true) => 2,
        };
        let mut fields = vec![(Operand::word(kind), Heapness::Static(false))];
        for (name, op) in &h.ops {
            let ExprKind::Closure(params, body) = &op.kind else {
                continue;
            };
            let closure = self.closure_of(params, body, op, true);
            fields.push((Operand::word(hash(name)), Heapness::Static(false)));
            fields.push((closure, Heapness::Static(true)));
        }
        self.alloc(0, fields)
    }

    /// `with h { block }` (handlers.with), of type `ty`.
    pub(crate) fn with_(&mut self, h: &Expr, effect: &Item, b: &Block, ty: &Ty) -> Vec<Operand> {
        let handler = self.expr1(h);
        let loc = self.loc_at(h.at);
        let id = Operand::word(effect_id(effect));
        let node = self.rt(
            Repr::Scalar,
            Runtime::Effects(Effects::Enter),
            vec![id, handler],
        );
        let node = self
            .b
            .define_op(Repr::Scalar, crate::mir::Rvalue::Use(node));
        let Operand::Local(node) = node else {
            unreachable!("a definition is a local")
        };
        let control = matches!(&h.ty, Ty::Handler(t) if t.answer.is_some());
        let outer = self.catchers.last().map_or(&self.err.ty, |c| &c.ty).clone();
        let error = if outer == Ty::Error {
            vec![self.b.temp(Repr::Heap)]
        } else {
            self.temps(&outer)
        };
        let (arms, join) = (self.b.new_block(), self.b.new_block());
        let result = self.temps(ty);
        self.catchers.push(Catcher {
            ty: outer,
            error: error.clone(),
            arms,
        });
        self.withs.push(Exit::With(node));
        let v = self.block(b);
        self.withs.pop();
        self.catchers.pop();
        let v = if control {
            let x = self.boxed(v, ty);
            self.finish_with(node, x, ty, loc.clone())
        } else {
            self.leave(node);
            v
        };
        self.into(&result, &v, join);
        self.b.switch_to(arms);
        if control {
            self.take_abort((node, loc), ty, &result, join);
        }
        self.leave(node);
        self.raise(operands(&error));
        self.b.switch_to(join);
        operands(&result)
    }

    /// At the `catch` of a `with` whose handler takes control: an abort that ends this `with`
    /// gives its value to the bodies that wait, as the block's end does (handlers.resuming).
    fn take_abort(
        &mut self,
        (node, loc): (Local, Operand),
        ty: &Ty,
        result: &[Local],
        join: crate::mir::BlockId,
    ) {
        let (mine, other) = (self.b.new_block(), self.b.new_block());
        let to_this = self.rt(
            Repr::Scalar,
            Runtime::Effects(Effects::AbortingTo),
            vec![Operand::Local(node)],
        );
        self.b.branch(to_this, mine, other);
        self.b.switch_to(mine);
        let repr = self.repr(ty);
        let answer = self.rt(repr, Runtime::Effects(Effects::AbortTake), Vec::new());
        let v = self.finish_with(node, answer, ty, loc);
        self.into(result, &v, join);
        self.b.switch_to(other);
    }

    /// Ends a `with` whose handler takes control, with the block's value `x` in one word, which
    /// the bodies that wait take, the latest first, each giving its own.
    fn finish_with(&mut self, node: Local, x: Operand, ty: &Ty, loc: Operand) -> Vec<Operand> {
        let code = self.rt(
            Repr::Heap,
            Runtime::Effects(Effects::Code),
            vec![Operand::word(FINISH)],
        );
        let err = self.catchers.last().map_or(&self.err.ty, |c| &c.ty).clone();
        let args = vec![
            Arg::Borrow(Operand::Local(node)),
            Arg::Own(x),
            Arg::Borrow(Operand::word(self.error_words(&err))),
        ];
        let (ret, err) = (Conv::boxed(ty.clone()), Conv::boxed(err));
        self.finish_call(Callee::Value(code), args, &[], loc, true, &ret, &err)
    }

    /// Removes the handler of a `with`.
    fn leave(&mut self, node: Local) {
        self.b.emit(Stmt::Effect(
            Runtime::Effects(Effects::Leave),
            vec![Operand::Local(node)],
        ));
    }

    /// Ends the `with`s and `when`s that a jump leaves: those past the first `depth`.
    pub(crate) fn leave_withs(&mut self, depth: usize) {
        for exit in self.withs.clone().into_iter().skip(depth).rev() {
            match exit {
                Exit::With(node) => self.leave(node),
                Exit::When(handles) => self.release(&handles),
            }
        }
    }

    /// At a `catch`'s arms: an abort passes on, as the raise of an error of zeros.
    pub(crate) fn pass_aborts(&mut self) {
        let (abort, handle) = (self.b.new_block(), self.b.new_block());
        let aborting = self.rt(
            Repr::Scalar,
            Runtime::Effects(Effects::Aborting),
            Vec::new(),
        );
        self.b.branch(aborting, abort, handle);
        self.b.switch_to(abort);
        let words = match self.catchers.last() {
            Some(c) => vec![Operand::word(0); c.error.len()],
            None if self.err.ty == Ty::Error => vec![Operand::word(0)],
            None => self.zeros(&self.err.ty.clone()),
        };
        self.raise(words);
        self.b.switch_to(handle);
    }

    /// The number of words of an error that a closure of the runtime writes to memory: those of
    /// its type when it has several, and otherwise none.
    fn error_words(&self, ty: &Ty) -> u64 {
        if *ty == Ty::Error {
            return 0;
        }
        if self.one_word(ty) {
            0
        } else {
            self.words_of(ty) as u64
        }
    }

    /// `resume(v)` (handlers.resuming): its value, of the `with`'s type, is that of the rest of the
    /// block.
    pub(crate) fn resume_(&mut self, v: Option<&Expr>, e: &Expr) -> Vec<Operand> {
        let (words, ty) = match v {
            Some(x) => (self.expr(x), x.ty.clone()),
            None => (vec![Operand::word(0)], Ty::unit()),
        };
        let v = self.boxed(words, &ty);
        let code = self.rt(
            Repr::Heap,
            Runtime::Effects(Effects::Code),
            vec![Operand::word(RESUME)],
        );
        let loc = self.loc_at(e.at);
        let (ret, err) = (Conv::boxed(e.ty.clone()), Conv::boxed(Ty::Error));
        self.finish_call(
            Callee::Value(code),
            vec![Arg::Own(v)],
            &[],
            loc,
            true,
            &ret,
            &err,
        )
    }

    /// Performs operation `op` of `effect` on its arguments, which go in one box
    /// (handlers.performing-operation).
    pub(crate) fn perform(
        &mut self,
        effect: &Item,
        op: Name,
        args: &[tast::Arg],
        row: &Row,
        e: &Expr,
    ) -> Vec<Operand> {
        let mut fields = Vec::new();
        for a in args {
            let words = self.expr(&a.value);
            let layout = self.layout(&a.value.ty);
            fields.extend(
                words
                    .into_iter()
                    .zip(layout)
                    .map(|(w, r)| (w, Heapness::of(r))),
            );
        }
        let boxed = if fields.is_empty() {
            Operand::word(0)
        } else {
            self.alloc(BOX, fields)
        };
        let err = error_type(row);
        let words = self.error_words(&err);
        let code = self.rt(
            Repr::Heap,
            Runtime::Effects(Effects::Code),
            vec![Operand::word(PERFORM)],
        );
        let args = vec![
            Arg::Borrow(Operand::word(effect_id(effect))),
            Arg::Borrow(Operand::word(hash(&op))),
            Arg::Borrow(boxed),
            Arg::Borrow(Operand::word(words)),
        ];
        let loc = self.loc_at(e.at);
        let (ret, err) = (Conv::boxed(e.ty.clone()), Conv::boxed(err));
        self.finish_call(Callee::Value(code), args, &[], loc, true, &ret, &err)
    }
}

#[cfg(test)]
mod tests {
    /// The runtime finds the `with`s of `async` by this hash (`stilt_runtime`'s `effects`).
    #[test]
    fn async_hashes_as_the_runtime_expects() {
        assert_eq!(super::hash("std.prelude.async"), 0x0a06_0b52_16f4_942b);
    }
}
