//! The bounds checks of element writes. A write whose index the facts prove in bounds of the list
//! that its slot's place holds loses its check, and still makes the list unique; every other write
//! keeps its check, so that it panics as it did (std.lists).

use super::{LOC, SHAPE, assign, counted_loop, decl, op, optimized, prim};
use crate::FnRef;
use crate::mir::{
    Arg, Block, BlockId, Callee, Function, Local, NumKind, Operand, Param, ParamMode, Prim, Repr,
    Runtime, Rvalue, Stmt, Terminator,
};

/// The slot of element `i`, checked, of the list the pointer `_p` reaches.
pub(super) fn slot(p: u32, i: Operand) -> Rvalue {
    Rvalue::Runtime(Runtime::ListSlot, vec![LOC, op(p), i, SHAPE])
}

/// The same, unchecked.
pub(super) fn slot_at(p: u32, i: Operand) -> Rvalue {
    Rvalue::Runtime(Runtime::ListSlotAt, vec![op(p), i, SHAPE])
}

/// `*_p = 0`.
pub(super) fn store(p: u32) -> Stmt {
    Stmt::Store {
        slot: op(p),
        value: Operand::word(0),
        repr: Repr::Scalar,
    }
}

/// The counter's step.
fn step() -> Stmt {
    prim(4, Prim::AddWrap(NumKind::I64), &[op(4), Operand::word(1)])
}

/// `for i in 0..xs.len() { body }` on the `inout` list `*_1`, measured through `_7`: the
/// counter is `_4`, and `body` may use `scalars` more locals from `_8`.
pub(super) fn inout_loop(body: Vec<Stmt>, scalars: usize) -> Function {
    let mut f = counted_loop(7, Rvalue::Use(Operand::word(0)));
    f.params[1].mode = ParamMode::Ref;
    f.locals.push(decl(Repr::Heap, false));
    f.locals
        .extend((0..scalars).map(|_| decl(Repr::Scalar, false)));
    f.blocks[0].stmts = vec![assign(7, Rvalue::Load(op(1)))];
    f.blocks[3].stmts = body;
    f.blocks[3].stmts.push(step());
    f
}

/// `var xs = ..; for i in 0..xs.len() { body }` on the list in the slot `_7`, measured through
/// `_8`: the counter is `_4`, the pointer `_9` is `&xs`, and `body` may use the scalar `_10`.
fn variable_loop(body: Vec<Stmt>) -> Function {
    let mut f = inout_loop(Vec::new(), 0);
    f.params[1].mode = ParamMode::Borrowed;
    f.locals[7] = decl(Repr::Heap, true);
    let scalar = decl(Repr::Scalar, false);
    f.locals
        .extend([decl(Repr::Heap, false), scalar.clone(), scalar]);
    f.blocks[0].stmts = vec![assign(8, Rvalue::Use(op(7)))];
    f.blocks[0].term = Terminator::Call {
        callee: Callee::Direct(super::list_len()),
        args: vec![Arg::Borrow(LOC), Arg::Borrow(op(8))],
        dest: vec![Local(3)],
        next: BlockId(1),
        raised: None,
    };
    f.blocks[3].stmts = vec![assign(9, Rvalue::SlotOf(Local(7)))];
    f.blocks[3].stmts.extend(body);
    f.blocks[3].stmts.push(step());
    f
}

#[test]
fn an_element_written_below_its_lists_length_needs_no_bounds_check() {
    let f = inout_loop(vec![assign(8, slot(1, op(4))), store(8)], 1);
    assert_eq!(optimized(f, 8), [slot_at(1, op(4))]);
}

#[test]
fn an_element_of_a_list_variable_written_in_bounds_needs_no_bounds_check() {
    let f = variable_loop(vec![assign(10, slot(9, op(4))), store(10)]);
    assert_eq!(optimized(f, 10), [slot_at(9, op(4))]);
}

#[test]
fn a_write_after_one_at_the_same_index_needs_no_bounds_check() {
    // `xs[k] = 0` twice on `*_1`, `k` being the parameter `_10`: the first panics unless `k`
    // is in bounds, and writing an element leaves the list's length as it was.
    let k = op(10);
    let body = vec![
        assign(8, slot(1, k.clone())),
        store(8),
        assign(9, slot(1, k.clone())),
        store(9),
    ];
    let mut f = inout_loop(body, 3);
    f.params.push(Param {
        local: Local(10),
        mode: ParamMode::Borrowed,
    });
    assert_eq!(optimized(f.clone(), 8), [slot(1, k.clone())]);
    assert_eq!(optimized(f, 9), [slot_at(1, k)]);
}

#[test]
fn a_write_after_an_append_keeps_its_bounds_check() {
    // `xs.push(i)` then `xs[i] = 0`, on the list in the slot `_7`.
    let append = Stmt::Effect(Runtime::ListAppend, vec![op(9), SHAPE, op(4)]);
    let f = variable_loop(vec![append, assign(10, slot(9, op(4))), store(10)]);
    assert_eq!(optimized(f, 10), [slot(9, op(4))]);
}

#[test]
fn a_write_after_a_call_given_the_list_inout_keeps_its_bounds_check() {
    // `xs.pop()` then `xs[i] = 0`, on `*_1`: the call ends block 3, and block 5 writes.
    let mut f = inout_loop(Vec::new(), 1);
    f.blocks[3] = Block {
        stmts: Vec::new(),
        term: Terminator::Call {
            callee: Callee::Direct(FnRef::Main),
            args: vec![Arg::Borrow(LOC), Arg::Ref(op(1))],
            dest: Vec::new(),
            next: BlockId(5),
            raised: None,
        },
    };
    f.blocks.push(Block {
        stmts: vec![assign(8, slot(1, op(4))), store(8), step()],
        term: Terminator::Goto(BlockId(2)),
    });
    assert_eq!(optimized(f, 8), [slot(1, op(4))]);
}

#[test]
fn a_write_after_the_list_is_replaced_keeps_its_bounds_check() {
    // `xs = ys` then `xs[i] = 0`, on `*_1`.
    let replace = Stmt::Store {
        slot: op(1),
        value: op(2),
        repr: Repr::Heap,
    };
    let f = inout_loop(vec![replace, assign(8, slot(1, op(4))), store(8)], 1);
    assert_eq!(optimized(f, 8), [slot(1, op(4))]);
}

#[test]
fn a_write_past_the_counter_keeps_its_bounds_check() {
    // `xs[i + 1] = 0` can write `xs[xs.len()]`.
    let next = prim(9, Prim::Add(NumKind::I64), &[op(4), Operand::word(1)]);
    let f = inout_loop(vec![next, assign(8, slot(1, op(9))), store(8)], 2);
    assert_eq!(optimized(f, 8), [slot(1, op(9))]);
}

#[test]
fn a_write_to_another_list_than_the_one_measured_keeps_its_bounds_check() {
    // `for i in 0..ys.len() { xs[i] = 0 }`, `xs` being `*_1` and `ys` being `_2`.
    let mut f = counted_loop(2, Rvalue::Use(Operand::word(0)));
    f.params[1].mode = ParamMode::Ref;
    f.locals.push(decl(Repr::Scalar, false));
    f.blocks[3].stmts = vec![assign(7, slot(1, op(4))), store(7), step()];
    assert_eq!(optimized(f, 7), [slot(1, op(4))]);
}

#[test]
fn a_write_into_a_list_that_an_element_holds_keeps_its_bounds_check() {
    // `xs[i][i] = 0` on the list of lists `*_1`: `i` is in bounds of `xs`, which no fact
    // relates to the list `xs[i]`, reached through a pointer into an element.
    let lists = Operand::word(crate::shape::word(true));
    let outer = Rvalue::Runtime(Runtime::ListSlot, vec![LOC, op(1), op(4), lists.clone()]);
    let body = vec![assign(8, outer), assign(9, slot(8, op(4))), store(9)];
    let f = inout_loop(body, 2);
    let outer_at = Rvalue::Runtime(Runtime::ListSlotAt, vec![op(1), op(4), lists]);
    assert_eq!(optimized(f.clone(), 8), [outer_at]);
    assert_eq!(optimized(f, 9), [slot(8, op(4))]);
}
