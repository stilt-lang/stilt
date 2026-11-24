//! The locals of a list's header stay right around a loop that writes the list's elements, and
//! are given up at what may change the list.

use stilt_mir::FnRef;
use stilt_mir::mir::{
    Arg, Block, BlockId, Callee, Function, Local, LocalDecl, Operand, Param, ParamMode, Repr,
    Runtime, Rvalue, Stmt, Terminator,
};

use super::{Key, Lists};

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

const ELEM: Operand = Operand::word(stilt_mir::shape::word(false));

/// `var xs = list; loop { xs[0] = 7; ends }`: `_1` the list, `_2` the place, `_3` its slot,
/// `_4` an element's, with `ends` the loop's terminator back to block 1.
fn writing_loop(ends: Terminator) -> Function {
    let local = |i: u32| Operand::Local(Local(i));
    let element = Rvalue::Runtime(
        Runtime::ListElement,
        vec![Operand::word(0), local(3), Operand::word(0), ELEM],
    );
    Function {
        name: FnRef::Main,
        params: vec![Param {
            local: Local(1),
            mode: ParamMode::Owned,
        }],
        hidden: 1,
        results: 0,
        locals: vec![
            decl(Repr::Scalar, false),
            decl(Repr::Heap, false),
            decl(Repr::Heap, true),
            decl(Repr::Scalar, false),
            decl(Repr::Scalar, false),
        ],
        blocks: vec![
            Block {
                stmts: vec![Stmt::Assign(Local(2), Rvalue::Use(local(1)))],
                term: Terminator::Goto(BlockId(1)),
            },
            Block {
                stmts: vec![
                    Stmt::Assign(Local(3), Rvalue::SlotOf(Local(2))),
                    Stmt::Assign(Local(4), element),
                    Stmt::Store {
                        slot: local(4),
                        value: Operand::word(7),
                        repr: Repr::Scalar,
                    },
                ],
                term: ends,
            },
        ],
        broken: false,
    }
}

#[test]
fn a_loop_that_writes_elements_keeps_the_header_from_its_start() {
    let lists = Lists::new(&writing_loop(Terminator::Goto(BlockId(1))));
    assert!(lists.ins[1].contains(&Key::Place(2)), "{:?}", lists.ins);
}

#[test]
fn a_call_in_the_loop_gives_the_header_up() {
    let call = Terminator::Call {
        callee: Callee::Direct(FnRef::Main),
        args: vec![Arg::Borrow(Operand::word(0))],
        dest: Vec::new(),
        next: BlockId(1),
        raised: None,
    };
    let lists = Lists::new(&writing_loop(call));
    assert!(!lists.ins[1].contains(&Key::Place(2)), "{:?}", lists.ins);
}

#[test]
fn a_store_to_the_place_gives_the_header_up() {
    let mut f = writing_loop(Terminator::Goto(BlockId(1)));
    f.blocks[1].stmts.push(Stmt::Store {
        slot: Operand::Local(Local(3)),
        value: Operand::Local(Local(1)),
        repr: Repr::Heap,
    });
    let lists = Lists::new(&f);
    assert!(!lists.ins[1].contains(&Key::Place(2)), "{:?}", lists.ins);
}

/// `fn f(inout xs) { loop { xs[0] = 7; ends } }`: `_1` the pointer to the caller's slot, `_2` an
/// element's slot, with `ends` the loop's terminator back to block 1.
fn inout_loop(ends: Terminator) -> Function {
    let local = |i: u32| Operand::Local(Local(i));
    let element = Rvalue::Runtime(
        Runtime::ListElementAt,
        vec![local(1), Operand::word(0), ELEM],
    );
    Function {
        name: FnRef::Main,
        params: vec![Param {
            local: Local(1),
            mode: ParamMode::Ref,
        }],
        hidden: 1,
        results: 0,
        locals: vec![
            decl(Repr::Scalar, false),
            decl(Repr::Scalar, false),
            decl(Repr::Scalar, false),
        ],
        blocks: vec![
            Block {
                stmts: vec![Stmt::Effect(Runtime::Unique, vec![local(1)])],
                term: Terminator::Goto(BlockId(1)),
            },
            Block {
                stmts: vec![
                    Stmt::Assign(Local(2), element),
                    Stmt::Store {
                        slot: local(2),
                        value: Operand::word(7),
                        repr: Repr::Scalar,
                    },
                ],
                term: ends,
            },
        ],
        broken: false,
    }
}

#[test]
fn an_inout_parameter_s_list_keeps_its_header_across_the_loop() {
    // modes.overlapping-inout: nothing but the parameter reaches the caller's slot.
    let lists = Lists::new(&inout_loop(Terminator::Goto(BlockId(1))));
    assert!(lists.ins[1].contains(&Key::Place(1)), "{:?}", lists.ins);
    assert!(lists.is_pointed(1) && lists.params.is_empty());
}

#[test]
fn a_copied_inout_pointer_is_no_place() {
    let mut f = inout_loop(Terminator::Goto(BlockId(1)));
    f.blocks[0].stmts.push(Stmt::Assign(
        Local(2),
        Rvalue::Use(Operand::Local(Local(1))),
    ));
    let lists = Lists::new(&f);
    assert_eq!(lists.place_of(&Operand::Local(Local(1))), None);
}

#[test]
fn a_store_through_the_inout_pointer_gives_the_header_up() {
    let mut f = inout_loop(Terminator::Goto(BlockId(1)));
    f.blocks[1].stmts.push(Stmt::Store {
        slot: Operand::Local(Local(1)),
        value: Operand::word(0),
        repr: Repr::Heap,
    });
    let lists = Lists::new(&f);
    assert!(!lists.ins[1].contains(&Key::Place(1)), "{:?}", lists.ins);
}
