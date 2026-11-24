//! Scalar replacement of objects (Values and costs, "A cheap optimizer before Cranelift"): an
//! object that a function makes and only reads field by field, itself or through copies, is
//! replaced by the words of the fields it reads, and every other object stays.

use super::{assign, function, op, ret};
use crate::mir::{
    Arg, Block, BlockId, Callee, Function, Heapness, Local, Operand, ParamMode, Rvalue, Stmt,
    Terminator,
};
use crate::opt::boxes::unbox;

/// A box of the string `_1` and the scalar 7, in `_2`.
fn boxed() -> Stmt {
    let fields = vec![
        (op(1), Heapness::Static(true)),
        (Operand::word(7), Heapness::Static(false)),
    ];
    assign(2, Rvalue::Alloc(0, fields))
}

fn field(d: u32, base: u32, len: u32, index: u32) -> Stmt {
    assign(
        d,
        Rvalue::Field {
            base: op(base),
            len,
            index,
            variant: None,
        },
    )
}

/// A function of the string parameter `_1` and the locals `_2` to `_5`, the heap words `_2`
/// to `_4`, whose block runs `stmts` and returns.
fn with(stmts: Vec<Stmt>) -> Function {
    function(&[ParamMode::Borrowed], 4, &[1, 2, 3, 4], vec![ret(stmts)])
}

#[test]
fn an_object_read_field_by_field_is_replaced_by_the_fields_it_reads() {
    // `_3` copies the box, and only its string is read, into `_4`.
    let mut f = with(vec![
        boxed(),
        assign(3, Rvalue::Use(op(2))),
        field(4, 3, 2, 0),
    ]);
    assert!(unbox(&mut f));
    assert_eq!(
        f.blocks[0].stmts,
        [assign(6, Rvalue::Use(op(1))), assign(4, Rvalue::Use(op(6)))]
    );
    assert_eq!(f.locals.len(), 7);
}

#[test]
fn an_object_held_by_a_replaced_object_is_replaced_too() {
    // `_3` holds the box `_2`, and `_5` reads the string through both.
    let outer = assign(3, Rvalue::Alloc(0, vec![(op(2), Heapness::Static(true))]));
    let mut f = with(vec![boxed(), outer, field(4, 3, 1, 0), field(5, 4, 2, 0)]);
    assert!(unbox(&mut f));
    let allocates = f
        .blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .any(|s| matches!(s, Stmt::Assign(_, Rvalue::Alloc(..))));
    assert!(!allocates, "{:?}", f.blocks[0].stmts);
}

#[test]
fn an_object_that_a_call_takes_stays() {
    let call = Terminator::Call {
        callee: Callee::Direct(crate::FnRef::Main),
        args: vec![Arg::Borrow(super::LOC), Arg::Borrow(op(2))],
        dest: vec![Local(5)],
        next: BlockId(1),
        raised: None,
    };
    let blocks = vec![
        Block {
            stmts: vec![boxed(), field(4, 2, 2, 0)],
            term: call,
        },
        ret(Vec::new()),
    ];
    let mut f = function(&[ParamMode::Borrowed], 4, &[1, 2, 3, 4], blocks);
    let before = f.clone();
    assert!(!unbox(&mut f));
    assert_eq!(f, before);
}

#[test]
fn an_object_returned_stays() {
    let mut f = with(vec![boxed(), field(4, 2, 2, 0)]);
    f.blocks[0].term = Terminator::Return(vec![op(2)]);
    assert!(!unbox(&mut f));
}

#[test]
fn an_object_read_as_another_size_stays() {
    let mut f = with(vec![boxed(), field(4, 2, 3, 0)]);
    assert!(!unbox(&mut f));
}

#[test]
fn an_object_assigned_twice_stays() {
    let mut f = with(vec![boxed(), boxed(), field(4, 2, 2, 0)]);
    assert!(!unbox(&mut f));
}
