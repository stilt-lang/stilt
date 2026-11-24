//! Writable views (projections.writable-views and projections.places-through-views): the natives
//! `view.into`, `view.part` and `view.split`, which compile inline, and `v[i]` as a place. A
//! writable view is held as any view is, its source's word with a reference of its own and two
//! offsets (`super::views`), into storage that `into` and `split` have made unique first, as a
//! write to it would, so that the list its source holds and the view share one
//! object: a write through `v[i]` goes to that object without checking its count, since the law of
//! exclusivity keeps every other access away while the view's binding lives
//! (projections.reaching-written-source), and a view handed back in a result or copied out of a
//! yielded place still points at the caller's storage. `part` only narrows a view's offsets. Rule
//! numbers in comments refer to the Reference's projections chapter.

use stilt_types::tast::{self, Callee, Expr};
use stilt_types::ty::{Row, Ty};

use super::calls::{Forms, can_raise, error_type};
use super::lists::Elem;
use super::places::{Place, Step};
use super::words::word;
use super::{Conv, Lower};
use crate::mir::{Arg, NumKind, Operand, Prim, Repr, Runtime, Rvalue, Stmt, Views};
use crate::shape;

/// The native of `std.view` that an item names, if it makes writable views.
fn window(item: &stilt_hir::hir::Item) -> Option<&str> {
    (&*item.home == "std.view" && matches!(&*item.name, "into" | "part" | "split"))
        .then_some(&*item.name)
}

impl Lower<'_> {
    /// A call of `view.into`, `view.part` or `view.split`, if `callee` names one
    /// (projections.writable-views). Its `inout` argument is a place, read when the call starts and
    /// written back when it ends.
    pub(crate) fn window_call(
        &mut self,
        callee: &Callee,
        args: &[tast::Arg],
        e: &Expr,
    ) -> Option<Vec<Operand>> {
        let Callee::Function(item) = callee else {
            return None;
        };
        let name = window(item)?;
        let (values, writebacks) = self.arguments(args, &Forms::layout());
        let loc = self.loc_at(e.at);
        let row = args.get(2).map(|a| closure_row(&a.value.ty));
        let out = self.window_native(name, &values, loc, row.as_ref(), &writebacks);
        if name != "split" {
            self.write_back(&writebacks);
        }
        Some(out)
    }

    /// `view.into`, `view.part` or `view.split`, if `f` names one, on its arguments as a
    /// function used as a value gives them: a pointer for the `inout` one.
    pub(crate) fn inline_window(&mut self, f: &crate::FnRef, args: &[Arg]) -> Option<Vec<Operand>> {
        let crate::FnRef::Function(item) = f else {
            return None;
        };
        let name = window(item)?;
        let loc = Operand::Local(self.loc);
        Some(self.window_native(name, args, loc, None, &[]))
    }

    /// The native `name` on its arguments: a pointer to the list's or the view's words, then
    /// the offsets, or for `split`, the offset and the closure.
    fn window_native(
        &mut self,
        name: &str,
        args: &[Arg],
        loc: Operand,
        row: Option<&Row>,
        writebacks: &[super::places::Writeback],
    ) -> Vec<Operand> {
        let arg = |i: usize| -> Operand {
            args.get(i)
                .and_then(|a| a.operands().first().map(|o| (*o).clone()))
                .unwrap_or(Operand::word(0))
        };
        let (slot, a, b) = (arg(0), arg(1), arg(2));
        match name {
            "into" => {
                // The storage is made unique where it was shared, the one work `into` does.
                self.b
                    .emit(Stmt::Effect(Runtime::Unique, vec![slot.clone()]));
                let list = self.b.define_op(Repr::Heap, Rvalue::Load(slot));
                let args = vec![loc, list, a.clone(), b.clone()];
                let source = self.rt(Repr::Heap, Runtime::Views(Views::Of), args);
                vec![source, a, b]
            }
            "part" => {
                let (list, start, end) = self.view_words(&slot);
                let args = vec![loc, list, start.clone(), end, a.clone(), b.clone()];
                let source = self.rt(Repr::Heap, Runtime::Views(Views::Part), args);
                let s = self.add_offsets(start.clone(), a);
                let e = self.add_offsets(start, b);
                vec![source, s, e]
            }
            _ => {
                self.split(slot, a, b, loc, row, writebacks);
                vec![Operand::word(0)]
            }
        }
    }

    /// `view.split(inout xs, at, f)`: `f` called once with the parts of `xs` before and from
    /// `at`, each writable, the list made unique first. `f` is non-escaping, so what it raises
    /// passes through (effects.non-escaping-parameters).
    fn split(
        &mut self,
        slot: Operand,
        at: Operand,
        f: Operand,
        loc: Operand,
        row: Option<&Row>,
        writebacks: &[super::places::Writeback],
    ) {
        self.b
            .emit(Stmt::Effect(Runtime::Unique, vec![slot.clone()]));
        let list = self.b.define_op(Repr::Heap, Rvalue::Load(slot));
        let len = self.rt(Repr::Scalar, Runtime::Views(Views::Len), vec![list.clone()]);
        // `at..at` is in bounds exactly when `0 <= at <= xs.len()`, and each part holds a
        // reference of its own.
        let args = vec![loc.clone(), list.clone(), at.clone(), at.clone()];
        let before = self.rt(Repr::Heap, Runtime::Views(Views::Of), args);
        let args = vec![loc.clone(), list, at.clone(), len.clone()];
        let from = self.rt(Repr::Heap, Runtime::Views(Views::Of), args);
        let pointers: Vec<Operand> = [
            vec![before, Operand::word(0), at.clone()],
            vec![from, at, len],
        ]
        .into_iter()
        .map(|words| {
            let temps: Vec<_> = [Repr::Heap, Repr::Scalar, Repr::Scalar]
                .into_iter()
                .map(|r| self.b.temp(r))
                .collect();
            for (&t, w) in temps.iter().zip(words) {
                self.b.assign(t, Rvalue::Use(w));
            }
            self.b.make_slots(&temps);
            self.b.define_op(Repr::Scalar, Rvalue::SlotOf(temps[0]))
        })
        .collect();
        let args = pointers.into_iter().map(Arg::Ref).collect();
        let (raises, err) = match row {
            Some(row) => (can_raise(row), Conv::boxed(error_type(row))),
            None => (true, Conv::boxed(Ty::Error)),
        };
        let callee = crate::mir::Callee::Value(f);
        self.finish_call(
            callee,
            args,
            writebacks,
            loc,
            raises,
            &Conv::of(Ty::unit()),
            &err,
        );
    }

    /// The three words of the view that a pointer points to: its source, its start and its
    /// end.
    pub(crate) fn view_words(&mut self, slot: &Operand) -> (Operand, Operand, Operand) {
        let list = self.b.define_op(Repr::Heap, Rvalue::Load(slot.clone()));
        let at = self.offset(slot.clone(), 1);
        let start = self.b.define_op(Repr::Scalar, Rvalue::Load(at));
        let at = self.offset(slot.clone(), 2);
        let end = self.b.define_op(Repr::Scalar, Rvalue::Load(at));
        (list, start, end)
    }

    fn add_offsets(&mut self, a: Operand, b: Operand) -> Operand {
        let sum = Rvalue::Prim(Prim::AddWrap(NumKind::I64), vec![a, b], Operand::word(0));
        self.b.define_op(Repr::Scalar, sum)
    }

    /// A pointer to `v[i]` of the view whose words a pointer points to (views.functions-of-views
    /// and projections.places-through-views): the element of its source, in bounds, which no count
    /// is checked for, since the storage a writable binding writes is unique and nothing else
    /// reaches it while the binding lives.
    pub(crate) fn view_slot(&mut self, slot: Operand, step: &Step, elem: &Ty) -> Operand {
        let Step::Index { key, loc, .. } = step else {
            unreachable!("an index into a view")
        };
        let (_, start, end) = self.view_words(&slot);
        let args = vec![loc.clone(), start, end, word(key, 0)];
        let at = self.rt(Repr::Scalar, Runtime::Views(Views::Index), args);
        let shape = match self.elem(elem) {
            Elem::Inline { shape, .. } => shape,
            Elem::Dynamic(_) => shape::word(true),
        };
        let args = vec![slot, at, Operand::word(shape)];
        self.b
            .define_op(Repr::Scalar, Rvalue::Runtime(Runtime::ListElementAt, args))
    }

    /// The words of `v[i]`, borrowed, of the view given by its three words or by a pointer to
    /// them (views.functions-of-views).
    pub(crate) fn read_view_step(
        &mut self,
        before: Result<Vec<Operand>, Operand>,
        step: &Step,
        ty: &Ty,
    ) -> Vec<Operand> {
        let Step::Index { key, loc, .. } = step else {
            unreachable!("an index into a view")
        };
        let (list, start, end) = match before {
            Ok(v) => (word(&v, 0), word(&v, 1), word(&v, 2)),
            Err(p) => self.view_words(&p),
        };
        let args = vec![loc.clone(), start, end, word(key, 0)];
        let at = self.rt(Repr::Scalar, Runtime::Views(Views::Index), args);
        self.list_index(list, at, loc.clone(), ty)
    }

    /// `v[i] = x` on a view of elements of a type parameter held in one word, through the
    /// runtime, which converts the word, without a check of the source's count.
    pub(crate) fn view_put(&mut self, place: &Place, slot: &Operand, x: Operand) {
        let Some(Step::Index { key, loc, .. }) = place.steps.last() else {
            unreachable!("an index into a view")
        };
        let (list, start, end) = self.view_words(slot);
        let args = vec![loc.clone(), start, end, word(key, 0)];
        let at = self.rt(Repr::Scalar, Runtime::Views(Views::Index), args);
        let args = vec![loc.clone(), list, at, x];
        self.b.emit(Stmt::Effect(Runtime::Views(Views::Put), args));
    }
}

/// The row of a closure's type, or an empty one.
fn closure_row(ty: &Ty) -> Row {
    match ty {
        Ty::Fn(f) => f.row.clone(),
        _ => Row::EMPTY,
    }
}
