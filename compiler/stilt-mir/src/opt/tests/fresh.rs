//! A new list that a `var` takes is unique, so a release build's append to it and pop from it
//! check nothing of its count, and popping it keeps it so; a list that something else may
//! reference keeps every check.

use super::{LOC, SHAPE, assign, decl, function, op, ret};
use crate::FnRef;
use crate::mir::{
    Arg, Block, BlockId, Callee, Const, Function, Local, Operand, ParamMode, Repr, Runtime, Rvalue,
    Stmt, Terminator, UNIQUE_LIST,
};
use crate::opt::optimize_counted;
use stilt_hir::hir::{Item, Name};

/// `var xs = []` in the slot `_2`, made from the new list `_1`, with `_3` pointing to it,
/// then `between`, then an append of 7.
fn appended(between: Vec<Stmt>) -> Vec<Stmt> {
    let mut stmts = vec![
        assign(
            1,
            Rvalue::Runtime(Runtime::ListNew, vec![Operand::word(0), SHAPE]),
        ),
        assign(2, Rvalue::Use(op(1))),
        assign(3, Rvalue::SlotOf(Local(2))),
    ];
    stmts.extend(between);
    stmts.push(append());
    stmts
}

fn append() -> Stmt {
    Stmt::Effect(Runtime::ListAppend, vec![op(3), SHAPE, Operand::word(7)])
}

fn variable(blocks: Vec<Block>) -> Function {
    let mut f = function(&[], 6, &[1, 2, 5], blocks);
    f.locals[2] = decl(Repr::Heap, true);
    f
}

fn counted(mut f: Function) -> Vec<Vec<Stmt>> {
    optimize_counted(&mut f);
    crate::opt::in_place(&mut f);
    f.blocks.into_iter().map(|b| b.stmts).collect()
}

/// The append of 7 to the list `_3` points to, where it is, read into `list`.
fn in_place(list: u32) -> [Stmt; 2] {
    [
        assign(list, Rvalue::Load(op(3))),
        Stmt::Effect(Runtime::ListPush, vec![op(list), SHAPE, Operand::word(7)]),
    ]
}

#[test]
fn a_new_list_in_a_variable_is_appended_to_where_it_is() {
    let stmts = counted(variable(vec![ret(appended(Vec::new()))])).remove(0);
    assert_eq!(stmts[3..], in_place(7));
}

#[test]
fn a_new_list_that_something_else_references_is_appended_to_with_its_check() {
    // `let ys = xs` before the append: `_5` shares the list.
    let shared = vec![Stmt::Dup(Local(1)), assign(5, Rvalue::Use(op(1)))];
    let stmts = counted(variable(vec![ret(appended(shared))])).remove(0);
    assert_eq!(stmts.last(), Some(&append()));
}

/// The appended list given inout to `callee` in block 0, after `between`, then appended to in
/// block 1.
fn after_call(callee: FnRef) -> Function {
    after_call_and(callee, Vec::new())
}

fn after_call_and(callee: FnRef, between: Vec<Stmt>) -> Function {
    let mut first = ret(appended(between));
    first.stmts.pop();
    first.term = Terminator::Call {
        callee: Callee::Direct(callee),
        args: vec![Arg::Borrow(LOC), Arg::Borrow(SHAPE), Arg::Ref(op(3))],
        dest: vec![Local(4), Local(6)],
        next: BlockId(1),
        raised: None,
    };
    variable(vec![first, ret(vec![append()])])
}

fn list(member: &str) -> FnRef {
    FnRef::Member(
        Item {
            home: Name::from("std.prelude"),
            name: Name::from("List"),
        },
        Name::from(member),
    )
}

#[test]
fn a_popped_list_is_still_appended_to_where_it_is() {
    let blocks = counted(after_call(list("pop")));
    assert_eq!(blocks[1][..], in_place(7));
}

/// Whether the location of the call that ends block 0 says that it pops a unique list.
fn pops_unique(mut f: Function) -> bool {
    optimize_counted(&mut f);
    crate::opt::in_place(&mut f);
    matches!(&f.blocks[0].term, Terminator::Call { args, .. }
        if matches!(args[0], Arg::Borrow(Operand::Const(Const::Word(w))) if w & UNIQUE_LIST != 0))
}

#[test]
fn a_new_list_in_a_variable_is_popped_where_it_is() {
    assert!(pops_unique(after_call(list("pop"))));
}

#[test]
fn a_new_list_that_something_else_references_is_popped_with_its_check() {
    let shared = vec![Stmt::Dup(Local(1)), assign(5, Rvalue::Use(op(1)))];
    assert!(!pops_unique(after_call_and(list("pop"), shared)));
    assert!(
        !pops_unique(after_call(list("insert"))),
        "only a pop is marked"
    );
}

#[test]
fn a_list_given_inout_to_another_function_is_appended_to_with_its_check() {
    let blocks = counted(after_call(list("insert")));
    assert_eq!(blocks[1][..], [append()]);
    let mut f = after_call(FnRef::Main);
    f.params.push(crate::mir::Param {
        local: Local(5),
        mode: ParamMode::Borrowed,
    });
    assert_eq!(counted(f)[1][..], [append()]);
}
