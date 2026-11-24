use stilt_mir::mir::{Operand, Repr, Runtime, Rvalue, Stmt, Terminator};
use stilt_mir::shape;
use stilt_runtime::layout;

use crate::testing::{ClifBlock, block, clif, clif_blocks, function, heap, local, op, scalar};

/// Checks that the IR tests the bit of an object that threads share `tests` times, each test
/// branching to a cold block that calls the runtime.
fn tests_the_shared_bit(clif: &str, tests: usize) {
    let bit = format!("{:x}", layout::SHARED_BIT);
    let tested = clif
        .lines()
        .filter(|l| l.contains("iconst.i64") && l.replace('_', "").contains(&bit))
        .count();
    assert_eq!(tested, tests, "{clif}");
    let blocks = clif_blocks(clif);
    let cold_calls = blocks.iter().filter(|b| b.cold() && b.has("call")).count();
    assert!(cold_calls >= tests, "{clif}");
}

#[test]
fn a_count_of_an_object_threads_share_goes_through_the_runtime() {
    // `dup _1; drop _1` of a heap word.
    let f = function(
        &[heap()],
        &[],
        vec![block(
            vec![Stmt::Dup(local(1)), Stmt::Drop(local(1))],
            Terminator::Return(vec![Operand::word(0)]),
        )],
    );
    let clif = clif(&f);
    tests_the_shared_bit(&clif, 2);
    // The plain count is read from the word loaded once, and stored as 32 bits.
    assert!(clif.contains("load.i64"), "{clif}");
    assert!(clif.contains("ireduce.i32"), "{clif}");
    assert!(!clif.contains("load.i32"), "{clif}");
}

#[test]
fn a_write_to_a_list_threads_share_copies_it() {
    // `xs[i] = 0` on the list the slot `_1` holds, `i` being proved in bounds.
    let slot = Rvalue::Runtime(
        Runtime::ListSlotAt,
        vec![op(1), op(2), Operand::word(shape::word(false))],
    );
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
    let clif = clif(&f);
    tests_the_shared_bit(&clif, 1);
    // Both the bit and a count above 1 lead to the one cold block that copies the list.
    let blocks = clif_blocks(&clif);
    let copies: Vec<&ClifBlock<'_>> = blocks.iter().filter(|b| b.cold()).collect();
    assert_eq!(copies.len(), 1, "{clif}");
}
