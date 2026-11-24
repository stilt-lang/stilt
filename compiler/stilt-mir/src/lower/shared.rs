//! `when` (shared.when): each name of its block is the place of the value its handle
//! reaches, held in the `Shared<T>`'s object, which the block reads and writes through a
//! pointer to its words, as an `inout` parameter's are. Two names whose handles reach one value
//! so point to the same words, and are one place. The runtime is told each name, at the `when`'s
//! location, where it panics if a `when` around it holds the value
//! (shared.when-on-value-already-held), then holds them all, in their turn under `task.threads()`
//! (tasks.advanced-tier), and is told the end of the hold on each however the block ends: at its
//! end, at a raise out of it, and at a jump, as a `with` ends (`super::handlers`). The handles live
//! until then.

use stilt_hir::hir::LocalId;
use stilt_types::tast::{Block, Expr};
use stilt_types::ty::Ty;

use super::words::{operands, word};
use super::{Catcher, Exit, Lower, Var};
use crate::mir::{Operand, Repr, Runtime, Rvalue, Shared, Stmt};

impl Lower<'_> {
    /// `when` of the names `held` on the block `b`, the expression `e`.
    pub(crate) fn when_(&mut self, held: &[(Expr, LocalId)], b: &Block, e: &Expr) -> Vec<Operand> {
        let loc = self.loc_at(e.at);
        let mut handles = Vec::new();
        for (h, _) in held {
            let handle = word(&self.expr(h), 0);
            self.b.emit(Stmt::Effect(
                Runtime::Shared(Shared::Name),
                vec![loc.clone(), handle.clone()],
            ));
            handles.push(handle);
        }
        self.b
            .emit(Stmt::Effect(Runtime::Shared(Shared::Hold), Vec::new()));
        for ((_, place), handle) in held.iter().zip(&handles) {
            let pointer = self.b.define(
                Repr::Scalar,
                Rvalue::Runtime(Runtime::Shared(Shared::Place), vec![handle.clone()]),
            );
            self.vars.insert(*place, Var::Ref(pointer));
        }
        let outer = self.catchers.last().map_or(&self.err.ty, |c| &c.ty).clone();
        let error = if outer == Ty::Error {
            vec![self.b.temp(Repr::Heap)]
        } else {
            self.temps(&outer)
        };
        let (arms, join) = (self.b.new_block(), self.b.new_block());
        let result = self.temps(&e.ty);
        self.catchers.push(Catcher {
            ty: outer,
            error: error.clone(),
            arms,
        });
        self.withs.push(Exit::When(handles.clone()));
        let value = self.block(b);
        self.withs.pop();
        self.catchers.pop();
        self.release(&handles);
        self.into(&result, &value, join);
        self.b.switch_to(arms);
        self.release(&handles);
        self.raise(operands(&error));
        self.b.switch_to(join);
        operands(&result)
    }

    /// Ends a `when`'s hold on the values its handles reach.
    pub(crate) fn release(&mut self, handles: &[Operand]) {
        for handle in handles {
            self.b.emit(Stmt::Effect(
                Runtime::Shared(Shared::Leave),
                vec![handle.clone()],
            ));
        }
    }
}
