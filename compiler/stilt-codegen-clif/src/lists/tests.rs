use stilt_mir::mir::{Operand, Repr, Runtime, Rvalue, Stmt, Terminator};
use stilt_mir::shape;
use stilt_runtime::layout;

use crate::testing::{ClifBlock, LOC, block, clif, clif_blocks, function, heap, local, op, scalar};

/// The shape of a `bool`, which a list packs in a byte.
const BOOL: Operand = Operand::word(shape::packed(1, false));

/// The shape of a list's elements of one scalar word each.
const WORDS: Operand = Operand::word(shape::word(false));

#[test]
fn the_shapes_and_tags_of_the_mir_are_the_runtimes() {
    assert_eq!(shape::HEAP, layout::SHAPE_HEAP);
    assert_eq!(shape::SIGNED, layout::SHAPE_SIGNED);
    assert_eq!(shape::SIZE_SHIFT, layout::SHAPE_SIZE_SHIFT);
    assert_eq!(shape::SIZE_BITS, layout::SHAPE_SIZE_BITS);
    assert_eq!(shape::MASK_SHIFT, layout::SHAPE_MASK_SHIFT);
    assert_eq!(shape::MASK_WORDS, layout::MASK_WORDS);
    assert_eq!(shape::LARGE, layout::SHAPE_LARGE);
    assert_eq!(shape::SIZED, layout::SHAPE_SIZED);
    assert_eq!(stilt_mir::mir::SIGNED_ORDER, layout::SIGNED_ORDER);
    assert_eq!(stilt_mir::mir::UNSIGNED_ORDER, layout::UNSIGNED_ORDER);
    assert_eq!(stilt_mir::mir::WORD_KEYS, layout::WORD_KEYS);
    assert_eq!(stilt_mir::mir::STR_KEYS, layout::STR_KEYS);
    assert_eq!(stilt_mir::mir::BOX, layout::BOX);
    assert_eq!(stilt_mir::mir::INLINE_FIELDS, layout::INLINE_FIELDS);
    for (len, mask) in [
        (0, 0),
        (2, 3),
        (5, 0b1_0010),
        (30, u64::MAX),
        (31, 1),
        (700, 5),
    ] {
        assert_eq!(
            stilt_mir::mir::data_layout(len, mask),
            layout::data_layout(len, mask)
        );
    }
}

#[test]
fn a_packed_element_is_read_and_written_in_its_width() {
    // `xs[i] = !xs[i]` on a list of `bool`s that the slot `_1` holds, read from the list `_2`.
    let index = Rvalue::Runtime(
        Runtime::ListIndex,
        vec![LOC, op(2), op(3), BOOL, Operand::word(0)],
    );
    let slot = Rvalue::Runtime(Runtime::ListSlot, vec![LOC, op(1), op(3), BOOL]);
    let stmts = vec![
        Stmt::Assign(local(4), index),
        Stmt::Assign(local(5), slot),
        Stmt::Effect(Runtime::StorePacked, vec![op(5), op(4), BOOL]),
    ];
    let f = function(
        &[scalar(), heap(), scalar()],
        &[scalar(), scalar()],
        vec![block(stmts, Terminator::Return(vec![Operand::word(0)]))],
    );
    let clif = clif(&f);
    assert!(clif.contains("uload8.i64"), "{clif}");
    assert!(clif.contains("istore8"), "{clif}");
}

#[test]
fn an_append_with_room_in_a_unique_list_calls_nothing() {
    // `xs.push((a, b))` of two scalar words, on the list the slot `_1` holds.
    let pair = Operand::word(shape::sized(&[false, false]));
    let stmts = vec![Stmt::Effect(
        Runtime::ListAppend,
        vec![op(1), pair, op(2), op(3)],
    )];
    let f = function(
        &[scalar(), scalar(), scalar()],
        &[],
        vec![block(stmts, Terminator::Return(vec![Operand::word(0)]))],
    );
    let clif = clif(&f);
    let blocks = clif_blocks(&clif);
    for b in blocks.iter().filter(|b| !b.cold()) {
        assert!(!b.has("call"), "a call on the fast path:\n{clif}");
    }
    assert!(blocks.iter().any(|b| b.cold() && b.has("call")), "{clif}");
}

#[test]
fn a_write_in_bounds_checks_only_that_its_list_is_unique() {
    // `xs[i] = 0` on the list the slot `_1` holds, `i` being proved in bounds.
    let slot = Rvalue::Runtime(Runtime::ListSlotAt, vec![op(1), op(2), WORDS]);
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
    let blocks = clif_blocks(&clif);
    // Nothing fails, so nothing traps, and the hot path compares the list's count alone.
    assert!(blocks.iter().all(|b| !b.has("trap")), "{clif}");
    let hot: Vec<&str> = blocks
        .iter()
        .filter(|b| !b.cold())
        .flat_map(|b| b.insts.iter().copied())
        .collect();
    let compares = hot.iter().filter(|i| i.contains(" icmp")).count();
    assert_eq!(compares, 1, "{clif}");
    assert!(hot.iter().all(|i| !i.contains("call ")), "{clif}");
    // A shared list is copied in a cold block, which returns to the write.
    let copies: Vec<&str> = blocks
        .iter()
        .filter(|b| b.cold() && b.has("call"))
        .map(ClifBlock::ends_in)
        .collect();
    assert_eq!(copies, ["jump"], "{clif}");
}

/// The Cranelift IR's blocks of a function that writes 0 through the element's slot `slot`
/// takes, of the list the slot `_1` holds at the index `_2`.
fn written(slot: Rvalue) -> String {
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
    clif(&f)
}

#[test]
fn a_write_in_bounds_to_a_list_known_unique_checks_nothing() {
    let clif = written(Rvalue::Runtime(
        Runtime::ListElementAt,
        vec![op(1), op(2), WORDS],
    ));
    let blocks = clif_blocks(&clif);
    assert!(blocks.iter().all(|b| !b.cold() && !b.has("icmp")), "{clif}");
    assert!(blocks.iter().all(|b| !b.has("call")), "{clif}");
}

#[test]
fn a_write_to_a_list_known_unique_checks_only_its_bounds() {
    let clif = written(Rvalue::Runtime(
        Runtime::ListElement,
        vec![LOC, op(1), op(2), WORDS],
    ));
    let blocks = clif_blocks(&clif);
    let hot = blocks.iter().filter(|b| !b.cold());
    assert_eq!(
        hot.flat_map(|b| &b.insts)
            .filter(|i| i.contains(" icmp"))
            .count(),
        1
    );
    // The only call reports the index out of bounds, and never returns.
    let calls: Vec<&str> = blocks
        .iter()
        .filter(|b| b.has("call"))
        .map(ClifBlock::ends_in)
        .collect();
    assert_eq!(calls, ["trap"], "{clif}");
}

#[test]
fn making_a_list_unique_copies_it_in_a_cold_block() {
    let stmts = vec![Stmt::Effect(Runtime::Unique, vec![op(1)])];
    let f = function(
        &[scalar()],
        &[],
        vec![block(stmts, Terminator::Return(vec![Operand::word(0)]))],
    );
    let clif = clif(&f);
    let blocks = clif_blocks(&clif);
    assert!(
        blocks.iter().filter(|b| !b.cold()).all(|b| !b.has("call")),
        "{clif}"
    );
    let copies: Vec<&str> = blocks
        .iter()
        .filter(|b| b.cold() && b.has("call"))
        .map(ClifBlock::ends_in)
        .collect();
    assert_eq!(copies, ["jump"], "{clif}");
}

#[test]
fn an_appended_word_is_passed_in_a_slot_of_16_bytes() {
    // `xs.push(a)` of one scalar word: the slow path passes the word in memory, in a slot
    // whose size and alignment keep the float spills after it aligned.
    let stmts = vec![Stmt::Effect(Runtime::ListAppend, vec![op(1), WORDS, op(2)])];
    let f = function(
        &[scalar(), scalar()],
        &[],
        vec![block(stmts, Terminator::Return(vec![Operand::word(0)]))],
    );
    let clif = clif(&f);
    let slots: Vec<&str> = clif
        .lines()
        .filter(|l| l.contains("explicit_slot"))
        .collect();
    assert!(!slots.is_empty(), "{clif}");
    for slot in slots {
        assert!(slot.contains("explicit_slot 16, align = 16"), "{clif}");
    }
}
