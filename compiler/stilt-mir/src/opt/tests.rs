//! The checks the range facts discharge, and those they keep because they can fail.

use stilt_hir::hir::{Item, Name};

use super::optimize;
use crate::FnRef;
use crate::mir::{
    Arg, Block, BlockId, Callee, Function, Local, LocalDecl, NumKind, Operand, Param, ParamMode,
    Prim, Repr, Runtime, Rvalue, Stmt, Terminator,
};

mod arith;
mod bounds;
mod boxes;
mod copies;
mod fresh;
mod inline;
mod instance;
mod loops;
mod onto;
mod pushes;
mod steps;
mod unique;
mod writes;

const LOC: Operand = Operand::word(1 << 20 | 1);

/// The shape of a list's elements of one word, scalars.
const SHAPE: Operand = Operand::word(crate::shape::word(false));

fn decl(repr: Repr, slot: bool) -> LocalDecl {
    LocalDecl {
        repr,
        slot,
        grouped: false,
        borrowed: false,
        var: false,
        name: None,
        shown: None,
    }
}

fn op(i: u32) -> Operand {
    Operand::Local(Local(i))
}

fn assign(d: u32, r: Rvalue) -> Stmt {
    Stmt::Assign(Local(d), r)
}

fn prim(d: u32, p: Prim, args: &[Operand]) -> Stmt {
    assign(d, Rvalue::Prim(p, args.to_vec(), LOC))
}

fn goto(stmts: Vec<Stmt>, to: u32) -> Block {
    Block {
        stmts,
        term: Terminator::Goto(BlockId(to)),
    }
}

fn branch(stmts: Vec<Stmt>, cond: u32, then: u32, otherwise: u32) -> Block {
    Block {
        stmts,
        term: Terminator::Branch {
            cond: op(cond),
            then: BlockId(then),
            otherwise: BlockId(otherwise),
        },
    }
}

fn ret(stmts: Vec<Stmt>) -> Block {
    Block {
        stmts,
        term: Terminator::Return(vec![Operand::word(0)]),
    }
}

/// The standard library's `List.len`.
fn list_len() -> FnRef {
    FnRef::Member(
        Item {
            home: Name::from("std.prelude"),
            name: Name::from("List"),
        },
        Name::from("len"),
    )
}

/// A function whose parameters are its location, then `params`, and whose other locals are
/// `locals`, each a scalar unless its index is in `heap`.
fn function(params: &[ParamMode], locals: u32, heap: &[u32], blocks: Vec<Block>) -> Function {
    let count = 1 + u32::try_from(params.len()).expect("few parameters") + locals;
    let locals = (0..count)
        .map(|i| {
            let repr = if heap.contains(&i) {
                Repr::Heap
            } else {
                Repr::Scalar
            };
            decl(repr, false)
        })
        .collect();
    let modes = std::iter::once(ParamMode::Borrowed).chain(params.iter().copied());
    Function {
        name: FnRef::Main,
        params: modes
            .enumerate()
            .map(|(i, mode)| Param {
                local: Local(u32::try_from(i).expect("few parameters")),
                mode,
            })
            .collect(),
        hidden: 1,
        results: 1,
        locals,
        blocks,
        broken: false,
    }
}

/// The rvalues of a function's assignments to `d`, after optimizing it.
fn optimized(mut f: Function, d: u32) -> Vec<Rvalue> {
    optimize(&mut f);
    f.blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter_map(|s| match s {
            Stmt::Assign(l, r) if *l == Local(d) => Some(r.clone()),
            _ => None,
        })
        .collect()
}

/// `for i in 0..xs.len() { xs[i] }` over the list `_1`, `bound` giving the list whose length
/// bounds the loop, `_1` or `_2`. The counter is `_4`, the element `_6`.
fn counted_loop(bound: u32, index: Rvalue) -> Function {
    let len = Terminator::Call {
        callee: Callee::Direct(list_len()),
        args: vec![Arg::Borrow(LOC), Arg::Borrow(op(bound))],
        dest: vec![Local(3)],
        next: BlockId(1),
        raised: None,
    };
    let blocks = vec![
        Block {
            stmts: Vec::new(),
            term: len,
        },
        goto(vec![assign(4, Rvalue::Use(Operand::word(0)))], 2),
        branch(
            vec![prim(5, Prim::Lt(NumKind::I64), &[op(4), op(3)])],
            5,
            3,
            4,
        ),
        goto(
            vec![
                assign(6, index),
                prim(4, Prim::AddWrap(NumKind::I64), &[op(4), Operand::word(1)]),
            ],
            2,
        ),
        ret(Vec::new()),
    ];
    function(
        &[ParamMode::Borrowed, ParamMode::Borrowed],
        4,
        &[1, 2],
        blocks,
    )
}

fn index(list: u32, i: Operand) -> Rvalue {
    Rvalue::Runtime(
        Runtime::ListIndex,
        vec![LOC, op(list), i, SHAPE, Operand::word(0)],
    )
}

fn at(list: u32, i: Operand) -> Rvalue {
    Rvalue::Runtime(Runtime::ListAt, vec![op(list), i, SHAPE, Operand::word(0)])
}

#[test]
fn an_element_read_below_its_lists_length_needs_no_bounds_check() {
    let f = counted_loop(1, index(1, op(4)));
    assert_eq!(optimized(f, 6), [at(1, op(4))]);
}

#[test]
fn an_element_read_below_another_lists_length_keeps_its_check() {
    let f = counted_loop(2, index(1, op(4)));
    assert_eq!(optimized(f, 6), [index(1, op(4))]);
}

#[test]
fn an_element_read_past_the_counter_keeps_its_check() {
    // `xs[i + 1]` can be `xs[xs.len()]`.
    let mut f = counted_loop(1, index(1, op(7)));
    f.locals.push(decl(Repr::Scalar, false));
    f.blocks[3].stmts.insert(
        0,
        prim(7, Prim::Add(NumKind::I64), &[op(4), Operand::word(1)]),
    );
    assert_eq!(optimized(f, 6), [index(1, op(7))]);
}

#[test]
fn an_index_that_may_be_negative_keeps_its_check() {
    // The counter counts from a parameter, which may be below 0.
    let mut f = counted_loop(1, index(1, op(4)));
    f.params.push(Param {
        local: Local(7),
        mode: ParamMode::Borrowed,
    });
    f.locals.push(decl(Repr::Scalar, false));
    f.blocks[1].stmts = vec![assign(4, Rvalue::Use(op(7)))];
    assert_eq!(optimized(f, 6), [index(1, op(4))]);
}

#[test]
fn the_counters_step_needs_no_overflow_check() {
    let mut f = counted_loop(1, index(1, op(4)));
    f.blocks[3].stmts[1] = prim(4, Prim::Add(NumKind::I64), &[op(4), Operand::word(1)]);
    let steps = optimized(f, 4);
    assert_eq!(
        steps[1],
        Rvalue::Prim(
            Prim::AddWrap(NumKind::I64),
            vec![op(4), Operand::word(1)],
            LOC
        )
    );
}

/// `while i != n { body; i += 1 }`, which reaches the maximum when `n` is below the start,
/// unless `body` keeps `i` below another integer.
fn unbounded_loop(body: Vec<Stmt>) -> Function {
    let mut f = counted_loop(1, index(1, op(4)));
    f.blocks[2].stmts = vec![prim(5, Prim::WordEq, &[op(4), op(3)])];
    f.blocks[2].term = Terminator::Branch {
        cond: op(5),
        then: BlockId(4),
        otherwise: BlockId(3),
    };
    f.blocks[3].stmts = body;
    f.blocks[3]
        .stmts
        .push(prim(4, Prim::Add(NumKind::I64), &[op(4), Operand::word(1)]));
    f
}

#[test]
fn a_step_past_an_unbounded_test_keeps_its_overflow_check() {
    let rvalues = optimized(unbounded_loop(Vec::new()), 4);
    // Still checked, as numbers.integer-panics requires: the counter is at least 0, so its step can
    // only overflow past the maximum, and takes the check of such an addition.
    assert!(matches!(
        rvalues[1],
        Rvalue::Prim(Prim::AddUp(NumKind::I64), ..)
    ));
}

#[test]
fn a_step_after_its_counter_indexes_a_list_needs_no_overflow_check() {
    // Reading `xs[i]` puts `i` below the list's length, so its step can't overflow.
    let rvalues = optimized(unbounded_loop(vec![assign(6, index(1, op(4)))]), 4);
    assert!(matches!(
        rvalues[1],
        Rvalue::Prim(Prim::AddWrap(NumKind::I64), ..)
    ));
}

#[test]
fn a_list_pushed_onto_in_the_loop_keeps_its_bounds_check() {
    // The list in the slot `_7` is measured, then grows and shrinks through a call that
    // takes it `inout`, as `xs.pop()` does.
    let mut f = counted_loop(1, index(8, op(4)));
    f.locals.push(decl(Repr::Heap, true));
    f.locals.push(decl(Repr::Heap, false));
    f.locals.push(decl(Repr::Scalar, false));
    f.blocks[0].stmts = vec![assign(8, Rvalue::Use(op(7)))];
    f.blocks[0].term = Terminator::Call {
        callee: Callee::Direct(list_len()),
        args: vec![Arg::Borrow(LOC), Arg::Borrow(op(8))],
        dest: vec![Local(3)],
        next: BlockId(1),
        raised: None,
    };
    let pop = Terminator::Call {
        callee: Callee::Direct(FnRef::Main),
        args: vec![Arg::Borrow(LOC), Arg::Ref(op(9))],
        dest: Vec::new(),
        next: BlockId(2),
        raised: None,
    };
    f.blocks[3] = Block {
        stmts: vec![
            assign(9, Rvalue::SlotOf(Local(7))),
            assign(8, Rvalue::Use(op(7))),
            assign(6, index(8, op(4))),
            prim(4, Prim::AddWrap(NumKind::I64), &[op(4), Operand::word(1)]),
        ],
        term: pop,
    };
    assert_eq!(optimized(f, 6), [index(8, op(4))]);
}

#[test]
fn a_list_appended_to_in_the_loop_keeps_its_bounds_check() {
    // `xs.push(i)` on the list in the slot `_7`, after the loop reads `xs[i]`.
    let mut f = counted_loop(1, index(8, op(4)));
    f.locals
        .extend([decl(Repr::Heap, true), decl(Repr::Heap, false)]);
    f.locals.push(decl(Repr::Scalar, false));
    f.blocks[0].stmts = vec![assign(8, Rvalue::Use(op(7)))];
    f.blocks[0].term = Terminator::Call {
        callee: Callee::Direct(list_len()),
        args: vec![Arg::Borrow(LOC), Arg::Borrow(op(8))],
        dest: vec![Local(3)],
        next: BlockId(1),
        raised: None,
    };
    f.blocks[3].stmts = vec![
        assign(8, Rvalue::Use(op(7))),
        assign(6, index(8, op(4))),
        assign(9, Rvalue::SlotOf(Local(7))),
        Stmt::Effect(Runtime::ListAppend, vec![op(9), SHAPE, op(4)]),
        prim(4, Prim::AddWrap(NumKind::I64), &[op(4), Operand::word(1)]),
    ];
    assert_eq!(optimized(f, 6), [index(8, op(4))]);
}

#[test]
fn an_inout_list_written_through_its_elements_keeps_its_length() {
    // `xs[i] = 0` on the list `*_1`, which makes it unique, as a word, as a narrow scalar and
    // as a value of a type parameter, then reads `xs[i]` again.
    let mut f = counted_loop(7, index(8, op(4)));
    f.params[1].mode = ParamMode::Ref;
    f.locals.extend((0..3).map(|_| decl(Repr::Heap, false)));
    f.blocks[0].stmts = vec![assign(7, Rvalue::Load(op(1)))];
    let slot = Rvalue::Runtime(Runtime::ListSlot, vec![LOC, op(1), op(4), SHAPE]);
    let zero = Operand::word(0);
    let packed = Operand::word(crate::shape::packed(1, false));
    f.blocks[3].stmts = vec![
        assign(9, slot),
        Stmt::Store {
            slot: op(9),
            value: zero.clone(),
            repr: Repr::Scalar,
        },
        Stmt::Effect(Runtime::StorePacked, vec![op(9), zero.clone(), packed]),
        Stmt::Effect(Runtime::ListPut, vec![LOC, op(1), op(4), zero]),
        assign(8, Rvalue::Load(op(1))),
        assign(6, index(8, op(4))),
        prim(4, Prim::AddWrap(NumKind::I64), &[op(4), Operand::word(1)]),
    ];
    assert_eq!(optimized(f, 6), [at(8, op(4))]);
}

#[test]
fn an_inout_list_stored_to_keeps_its_bounds_check() {
    // `xs = ys` on `*_1` between the measure and the read.
    let mut f = counted_loop(7, index(8, op(4)));
    f.params[1].mode = ParamMode::Ref;
    f.locals.extend((0..2).map(|_| decl(Repr::Heap, false)));
    f.blocks[0].stmts = vec![assign(7, Rvalue::Load(op(1)))];
    f.blocks[3].stmts = vec![
        Stmt::Store {
            slot: op(1),
            value: op(2),
            repr: Repr::Heap,
        },
        assign(8, Rvalue::Load(op(1))),
        assign(6, index(8, op(4))),
        prim(4, Prim::AddWrap(NumKind::I64), &[op(4), Operand::word(1)]),
    ];
    assert_eq!(optimized(f, 6), [index(8, op(4))]);
}

#[test]
fn a_repeated_operation_copies_the_first_result() {
    // `(i + j) * (i + j + 1)`.
    let add = |d| prim(d, Prim::Add(NumKind::I64), &[op(1), op(2)]);
    let f = function(
        &[ParamMode::Borrowed, ParamMode::Borrowed],
        3,
        &[],
        vec![ret(vec![
            add(3),
            add(4),
            prim(5, Prim::Mul(NumKind::I64), &[op(3), op(4)]),
        ])],
    );
    assert_eq!(optimized(f, 4), [Rvalue::Use(op(3))]);
}

#[test]
fn an_operation_on_a_changed_operand_is_computed_again() {
    let add = |d| prim(d, Prim::Add(NumKind::I64), &[op(1), op(2)]);
    let f = function(
        &[ParamMode::Borrowed, ParamMode::Borrowed],
        2,
        &[],
        vec![ret(vec![add(3), assign(1, Rvalue::Use(op(3))), add(4)])],
    );
    assert!(matches!(
        optimized(f, 4)[..],
        [Rvalue::Prim(Prim::Add(_), ..)]
    ));
}

/// The blocks of `a && b` as lowering gives them, where `_1` and `_2` are the booleans `a`
/// and `!b`: block 0 copies `a` into `_3` and branches on it, block 1 computes `b` into `_3`,
/// and block 2 branches on `_3` to block 3 when both hold and to block 4 otherwise.
fn and_then(back: bool) -> Function {
    let both = branch(Vec::new(), 3, 3, 4);
    let mut blocks = vec![
        branch(vec![assign(3, Rvalue::Use(op(1)))], 1, 1, 2),
        goto(
            vec![
                prim(4, Prim::BoolNot, &[op(2)]),
                assign(3, Rvalue::Use(op(4))),
            ],
            2,
        ),
        both,
        ret(Vec::new()),
        ret(Vec::new()),
    ];
    if back {
        // The lone branch comes before the block that jumps to it.
        blocks.swap(1, 2);
        blocks[0].term = Terminator::Branch {
            cond: op(1),
            then: BlockId(2),
            otherwise: BlockId(1),
        };
        blocks[2].term = Terminator::Goto(BlockId(1));
    }
    function(&[ParamMode::Borrowed, ParamMode::Borrowed], 2, &[], blocks)
}

#[test]
fn the_branches_of_and_test_each_condition_once() {
    let mut f = and_then(false);
    optimize(&mut f);
    // The lone branch is gone; `a` false leads out at once, and `b` is tested by its block.
    let exits: Vec<&Terminator> = f.blocks.iter().map(|b| &b.term).collect();
    assert_eq!(f.blocks.len(), 4, "{exits:?}");
    assert_eq!(
        f.blocks[0].term,
        Terminator::Branch {
            cond: op(1),
            then: BlockId(1),
            otherwise: BlockId(3),
        }
    );
    // A branch on `!b` branches on `b`, its outcomes swapped.
    assert_eq!(
        f.blocks[1].term,
        Terminator::Branch {
            cond: op(2),
            then: BlockId(3),
            otherwise: BlockId(2),
        }
    );
}

#[test]
fn a_jump_back_to_a_lone_branch_stays_a_jump() {
    // A jump back polls the stop flag of a watched run.
    let mut f = and_then(true);
    optimize(&mut f);
    assert_eq!(f.blocks[2].term, Terminator::Goto(BlockId(1)));
}

#[test]
fn a_counter_tested_through_a_copy_is_bounded_too() {
    // `while i < xs.len() { xs[i]; i += 1 }`, whose test reads `i` into a temporary `_7`.
    let mut f = counted_loop(1, index(1, op(4)));
    f.locals.push(decl(Repr::Scalar, false));
    f.blocks[2].stmts = vec![
        assign(7, Rvalue::Use(op(4))),
        prim(5, Prim::Lt(NumKind::I64), &[op(7), op(3)]),
    ];
    f.blocks[3].stmts[1] = prim(4, Prim::Add(NumKind::I64), &[op(4), Operand::word(1)]);
    let mut g = f.clone();
    assert_eq!(optimized(f, 6), [at(1, op(4))]);
    optimize(&mut g);
    assert_eq!(
        g.blocks[3].stmts[1],
        prim(4, Prim::AddWrap(NumKind::I64), &[op(4), Operand::word(1)])
    );
}
