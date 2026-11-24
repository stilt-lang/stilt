//! Making a list unique once: before a loop that writes it in every iteration, and not again by a
//! write that follows another, while nothing can share the list between them (goal debug-speed).
//! Every write that something may have shared the list before keeps its check of the list's count.

use super::writes::{inout_loop, slot, slot_at, store};
use super::{LOC, SHAPE, assign, decl, function, goto, op, ret};
use crate::FnRef;
use crate::mir::{
    Arg, BlockId, Callee, Function, Local, Operand, ParamMode, Repr, Runtime, Rvalue, Stmt,
    Terminator,
};
use crate::opt::optimize_counted;

/// The element's slot of `slot_at` with the list known unique.
fn element_at(p: u32, i: u32) -> Rvalue {
    Rvalue::Runtime(Runtime::ListElementAt, vec![op(p), op(i), SHAPE])
}

/// The element's slot of `slot` with the list known unique.
fn element(p: u32, i: u32) -> Rvalue {
    Rvalue::Runtime(Runtime::ListElement, vec![LOC, op(p), op(i), SHAPE])
}

fn unique(p: u32) -> Stmt {
    Stmt::Effect(Runtime::Unique, vec![op(p)])
}

/// The statements of each block of `f` once its lists are made unique once.
fn counted(mut f: Function) -> Vec<Vec<Stmt>> {
    optimize_counted(&mut f);
    f.blocks.into_iter().map(|b| b.stmts).collect()
}

#[test]
fn a_loop_that_writes_an_inout_list_makes_it_unique_once_before_it() {
    // `for i in 0..xs.len() { xs[i] = 0 }` on `*_1`: block 1 enters the loop.
    let f = inout_loop(vec![assign(8, slot_at(1, op(4))), store(8)], 1);
    let blocks = counted(f);
    assert_eq!(blocks[1].last(), Some(&unique(1)));
    assert_eq!(blocks[3][0], assign(8, element_at(1, 4)));
}

#[test]
fn a_write_checked_in_bounds_keeps_its_bounds_check_in_a_unique_list() {
    let f = inout_loop(vec![assign(8, slot(1, op(4))), store(8)], 1);
    assert_eq!(counted(f)[3][0], assign(8, element(1, 4)));
}

/// `xs[k] = 0` twice on `*_1`, `k` being `_2`, with `between` in between.
fn two_writes(between: Vec<Stmt>) -> Function {
    let mut stmts = vec![assign(3, slot(1, op(2))), store(3)];
    stmts.extend(between);
    stmts.extend([assign(4, slot(1, op(2))), store(4)]);
    function(
        &[ParamMode::Ref, ParamMode::Borrowed],
        3,
        &[5],
        vec![ret(stmts)],
    )
}

#[test]
fn a_write_after_another_to_the_same_list_checks_nothing_of_its_count() {
    let stmts = counted(two_writes(Vec::new())).remove(0);
    assert_eq!(stmts[0], assign(3, slot(1, op(2))));
    assert_eq!(stmts[2], assign(4, element(1, 2)));
}

#[test]
fn a_write_after_the_list_is_copied_checks_its_count() {
    // `let ys = xs` between the writes: the copy shares the list.
    let copy = vec![assign(5, Rvalue::Load(op(1))), Stmt::Dup(Local(5))];
    let stmts = counted(two_writes(copy)).remove(0);
    assert_eq!(stmts[4], assign(4, slot(1, op(2))));
}

#[test]
fn a_write_after_the_list_is_replaced_checks_its_count() {
    let replace = Stmt::Store {
        slot: op(1),
        value: op(5),
        repr: Repr::Heap,
    };
    let stmts = counted(two_writes(vec![replace])).remove(0);
    assert_eq!(stmts[3], assign(4, slot(1, op(2))));
}

#[test]
fn a_write_after_the_list_goes_to_a_runtime_function_checks_its_count() {
    // `"{xs}"` between the writes: the runtime is given the list, which it could keep.
    let show = vec![
        assign(5, Rvalue::Load(op(1))),
        assign(5, Rvalue::Runtime(Runtime::ListShow, vec![LOC, op(5)])),
    ];
    let stmts = counted(two_writes(show)).remove(0);
    assert_eq!(stmts[4], assign(4, slot(1, op(2))));
}

#[test]
fn a_write_after_an_element_is_read_checks_nothing_of_its_count() {
    let read = vec![
        assign(5, Rvalue::Load(op(1))),
        assign(
            5,
            Rvalue::Runtime(Runtime::ListAt, vec![op(5), op(2), SHAPE, Operand::word(0)]),
        ),
    ];
    let stmts = counted(two_writes(read)).remove(0);
    assert_eq!(stmts[4], assign(4, element(1, 2)));
}

/// `inout_loop` whose body ends with a call given `arg`, then writes in a block of its own.
fn loop_with_call(arg: Arg) -> Function {
    let mut f = inout_loop(vec![assign(9, Rvalue::Load(op(1)))], 2);
    let write = f.blocks[3].stmts.split_off(1);
    f.blocks[3].term = Terminator::Call {
        callee: Callee::Direct(FnRef::Main),
        args: vec![Arg::Borrow(LOC), arg],
        dest: Vec::new(),
        next: BlockId(5),
        raised: None,
    };
    let mut stmts = vec![assign(8, slot_at(1, op(4))), store(8)];
    stmts.extend(write);
    f.blocks.push(goto(stmts, 2));
    f
}

#[test]
fn a_loop_that_gives_the_list_to_a_call_inout_writes_it_with_its_check() {
    let blocks = counted(loop_with_call(Arg::Ref(op(1))));
    assert!(!blocks[1].contains(&unique(1)));
    assert_eq!(blocks[5][0], assign(8, slot_at(1, op(4))));
}

#[test]
fn a_loop_that_gives_the_list_to_a_call_writes_it_with_its_check() {
    let blocks = counted(loop_with_call(Arg::Borrow(op(9))));
    assert!(!blocks[1].contains(&unique(1)));
    assert_eq!(blocks[5][0], assign(8, slot_at(1, op(4))));
}

#[test]
fn a_loop_that_gives_a_call_something_else_still_makes_the_list_unique_once() {
    let blocks = counted(loop_with_call(Arg::Borrow(op(4))));
    assert_eq!(blocks[1].last(), Some(&unique(1)));
    assert_eq!(blocks[5][0], assign(8, element_at(1, 4)));
}

#[test]
fn a_loop_that_writes_only_in_some_iterations_makes_nothing_unique_before_it() {
    // `if c { xs[i] = 0 }`: block 3 branches on `_9` to the write in block 5, and both go on
    // to block 6, which steps the counter.
    let mut f = inout_loop(Vec::new(), 2);
    let step = f.blocks[3].stmts.pop().expect("the step");
    f.blocks[3].term = Terminator::Branch {
        cond: op(9),
        then: BlockId(5),
        otherwise: BlockId(6),
    };
    f.blocks
        .push(goto(vec![assign(8, slot_at(1, op(4))), store(8)], 6));
    f.blocks.push(goto(vec![step], 2));
    let blocks = counted(f);
    assert!(!blocks[1].contains(&unique(1)));
    assert_eq!(blocks[5][0], assign(8, slot_at(1, op(4))));
}

/// `var ys = xs; for i in 0..ys.len() { ys[i] = 0 }`, `ys` in the slot `_7`, which block 0
/// assigns the list `_1` when `assigned`, and `_9` pointing to it.
fn variable_loop(assigned: bool) -> Function {
    let mut f = inout_loop(Vec::new(), 2);
    f.params[1].mode = ParamMode::Borrowed;
    f.locals[7] = decl(Repr::Heap, true);
    f.blocks[0].stmts.clear();
    if assigned {
        f.blocks[0].stmts.push(assign(7, Rvalue::Use(op(1))));
    }
    let step = f.blocks[3].stmts.pop().expect("the step");
    f.blocks[3].stmts = vec![
        assign(9, Rvalue::SlotOf(Local(7))),
        assign(8, slot_at(9, op(4))),
        store(8),
        step,
    ];
    f
}

#[test]
fn a_loop_that_writes_a_list_variable_makes_it_unique_once_before_it() {
    let blocks = counted(variable_loop(true));
    let pointer = Local(10);
    assert_eq!(
        blocks[1][1..],
        [
            Stmt::Assign(pointer, Rvalue::SlotOf(Local(7))),
            unique(pointer.0),
        ]
    );
    assert_eq!(blocks[3][1], assign(8, element_at(9, 4)));
}

#[test]
fn a_list_variable_not_yet_assigned_isnt_made_unique_before_the_loop() {
    let blocks = counted(variable_loop(false));
    assert_eq!(blocks[1].len(), 1);
    assert_eq!(blocks[3][1], assign(8, slot_at(9, op(4))));
}

#[test]
fn a_list_made_unique_by_a_loop_needs_nothing_again_in_the_next() {
    // Two loops one after the other, each writing `*_1`: the first loop's exit, block 4, enters
    // a copy of its blocks 1 to 4 as blocks 5 to 8, where the list is still unique. The copy
    // takes the element's slot in `_9`.
    let f = inout_loop(vec![assign(8, slot_at(1, op(4))), store(8)], 2);
    let mut g = f.clone();
    g.blocks[4].term = Terminator::Goto(BlockId(5));
    for mut b in f.blocks.into_iter().skip(1) {
        retarget(&mut b.term, 4);
        g.blocks.push(b);
    }
    g.blocks[7]
        .stmts
        .splice(0..2, [assign(9, slot_at(1, op(4))), store(9)]);
    let blocks = counted(g);
    assert_eq!(blocks[1].last(), Some(&unique(1)));
    assert!(!blocks[5].contains(&unique(1)));
    assert_eq!(blocks[7][0], assign(9, element_at(1, 4)));
}

/// Adds `by` to each block a terminator goes to.
fn retarget(t: &mut Terminator, by: u32) {
    match t {
        Terminator::Goto(b) => b.0 += by,
        Terminator::Branch {
            then, otherwise, ..
        } => {
            then.0 += by;
            otherwise.0 += by;
        }
        _ => {}
    }
}
