use stilt_mir::mir::{BlockId, NumKind, Operand, Prim, Repr, Runtime, Rvalue, Stmt, Terminator};

use crate::testing::{
    LOC, block, clif, clif_blocks, float_loop, function, heap, local, op, prim, scalar,
};

/// The shape of a list's elements of one scalar word each, and the first word of an element.
const WORDS: Operand = Operand::word(stilt_mir::shape::word(false));
const WORD_0: Operand = Operand::word(0);

/// Checks that every call of a function's code is in a cold block, and returns the opcodes
/// that end the cold blocks that call.
fn cold_calls(clif: &str) -> Vec<String> {
    let blocks = clif_blocks(clif);
    for b in blocks.iter().filter(|b| !b.cold()) {
        assert!(!b.has("call"), "a call on the hot path:\n{clif}");
    }
    blocks
        .iter()
        .filter(|b| b.cold() && b.has("call"))
        .map(|b| b.ends_in().to_owned())
        .collect()
}

#[test]
fn an_overflow_panics_in_a_cold_block_that_ends_in_a_trap() {
    let stmts = vec![prim(2, Prim::Add(NumKind::I64), &[op(1), op(1)])];
    let f = function(
        &[scalar()],
        &[scalar()],
        vec![block(stmts, Terminator::Return(vec![op(2)]))],
    );
    assert_eq!(cold_calls(&clif(&f)), ["trap"]);
}

#[test]
fn the_checks_of_a_float_loop_are_off_its_hot_path() {
    // The counter's overflow.
    assert_eq!(cold_calls(&clif(&float_loop())), ["trap"]);
}

#[test]
fn a_division_panics_in_cold_blocks_that_end_in_traps() {
    let stmts = vec![prim(3, Prim::Div(NumKind::I64), &[op(1), op(2)])];
    let f = function(
        &[scalar(), scalar()],
        &[scalar()],
        vec![block(stmts, Terminator::Return(vec![op(3)]))],
    );
    // Division by zero, and the overflow of the least value divided by -1.
    assert_eq!(cold_calls(&clif(&f)), ["trap", "trap"]);
}

#[test]
fn an_index_out_of_bounds_panics_in_a_cold_block_that_ends_in_a_trap() {
    // `xs[i] + xs[i]` on a list of floats, whose element is loaded as one.
    let index = Rvalue::Runtime(Runtime::ListIndex, vec![LOC, op(1), op(2), WORDS, WORD_0]);
    let stmts = vec![
        Stmt::Assign(local(3), index),
        prim(4, Prim::Add(NumKind::F64), &[op(3), op(3)]),
    ];
    let f = function(
        &[heap(), scalar()],
        &[scalar(), scalar()],
        vec![block(stmts, Terminator::Return(vec![op(4)]))],
    );
    let clif = clif(&f);
    assert_eq!(cold_calls(&clif), ["trap"]);
    assert!(clif.contains("load.f64"), "{clif}");
}

#[test]
fn a_write_out_of_bounds_panics_in_a_cold_block_and_a_shared_list_is_copied_in_another() {
    // `xs[i] = 0` on the list the slot `_1` holds.
    let slot = Rvalue::Runtime(Runtime::ListSlot, vec![LOC, op(1), op(2), WORDS]);
    let stmts = vec![
        Stmt::Assign(local(3), slot),
        Stmt::Store {
            slot: op(3),
            value: Operand::word(0),
            repr: Repr::Scalar,
        },
    ];
    let f = function(
        &[scalar(), scalar()],
        &[scalar()],
        vec![block(stmts, Terminator::Return(vec![Operand::word(0)]))],
    );
    let mut ends = cold_calls(&clif(&f));
    ends.sort();
    // The copy returns to the write.
    assert_eq!(ends, ["jump", "trap"]);
}

#[test]
fn a_panic_the_program_writes_is_cold() {
    let blocks = vec![
        block(
            Vec::new(),
            Terminator::Branch {
                cond: op(1),
                then: BlockId(1),
                otherwise: BlockId(2),
            },
        ),
        block(
            Vec::new(),
            Terminator::Panic {
                kind: 7,
                detail: None,
                loc: LOC,
            },
        ),
        block(Vec::new(), Terminator::Return(vec![Operand::word(0)])),
    ];
    let f = function(&[scalar()], &[], blocks);
    assert_eq!(cold_calls(&clif(&f)), ["trap"]);
}
