//! Splicing a function's body in place of a call (Values and costs, "A cheap optimizer before
//! Cranelift"): the body reads the call's arguments, its location among them, so that the
//! standard library's code panics where the call is (program.panic-location); it returns into the
//! call's locals and raises by the call's raised edge; and its code is marked with the call's
//! location for a debugger (goal debuggable-builds).

use super::{LOC, assign, function, goto, op};
use crate::mir::{
    Arg, Block, BlockId, Callee, Function, Local, NumKind, Operand, ParamMode, Prim, Repr, Rvalue,
    Stmt, Terminator,
};
use crate::opt::inline::splice::{Body, splice};

/// The location word of the call in the caller.
const AT: u64 = 3 << 20 | 5;

/// `g(x) = x + 1`, with `x` in `_1`, which raises its argument instead when `raises`.
fn callee(raises: bool) -> Function {
    let add = Rvalue::Prim(
        Prim::Add(NumKind::I64),
        vec![op(1), Operand::word(1)],
        op(0),
    );
    let term = if raises {
        Terminator::Raise(vec![op(1)])
    } else {
        Terminator::Return(vec![op(2)])
    };
    let mut g = function(
        &[ParamMode::Borrowed],
        1,
        &[],
        vec![Block {
            stmts: vec![assign(2, add)],
            term,
        }],
    );
    g.locals[2].name = Some(stilt_hir::hir::Name::from("y"));
    g
}

/// `_2 = g(_1)`, then a return of `_2`, the call marked with [`AT`], with a raised edge into
/// `_3` when `raised`.
fn caller(raised: bool) -> Function {
    let call = Terminator::Call {
        callee: Callee::Direct(crate::FnRef::Main),
        args: vec![Arg::Borrow(LOC), Arg::Borrow(op(1))],
        dest: vec![Local(2)],
        next: BlockId(1),
        raised: raised.then(|| (vec![Local(3)], BlockId(2))),
    };
    let blocks = vec![
        Block {
            stmts: vec![Stmt::At(AT)],
            term: call,
        },
        Block {
            stmts: Vec::new(),
            term: Terminator::Return(vec![op(2)]),
        },
        Block {
            stmts: Vec::new(),
            term: Terminator::Raise(vec![op(3)]),
        },
    ];
    function(&[ParamMode::Borrowed], 2, &[], blocks)
}

fn spliced(mut f: Function, g: &Function, std: bool) -> Function {
    let body = Body {
        function: g,
        args: vec![LOC, op(1)],
        std,
    };
    assert!(splice(&mut f, BlockId(0), &body));
    f
}

#[test]
fn a_spliced_body_reads_the_calls_arguments_and_returns_into_its_locals() {
    let f = spliced(caller(false), &callee(false), true);
    assert_eq!(f.blocks[0].term, Terminator::Goto(BlockId(3)));
    // The location parameter and `x` stand for the call's location and `_1`, and the body's
    // own local is the caller's `_4`.
    let add = Rvalue::Prim(Prim::Add(NumKind::I64), vec![op(1), Operand::word(1)], LOC);
    assert_eq!(
        f.blocks[3],
        goto(
            vec![Stmt::At(AT), assign(4, add), assign(2, Rvalue::Use(op(4)))],
            1
        )
    );
    assert_eq!(f.locals.len(), 5);
}

#[test]
fn a_raise_in_the_body_leaves_by_the_calls_raised_edge() {
    let f = spliced(caller(true), &callee(true), true);
    assert_eq!(f.blocks[3].term, Terminator::Goto(BlockId(2)));
    assert_eq!(
        f.blocks[3].stmts.last(),
        Some(&assign(3, Rvalue::Use(op(1))))
    );
}

#[test]
fn a_raise_where_the_call_cant_raise_is_unreachable() {
    let f = spliced(caller(false), &callee(true), true);
    assert_eq!(f.blocks[3].term, Terminator::Unreachable);
}

#[test]
fn a_standard_library_local_has_no_name_in_the_caller_and_a_closures_keeps_its() {
    let std = spliced(caller(false), &callee(false), true);
    assert_eq!(std.locals[4].name, None);
    let closure = spliced(caller(false), &callee(false), false);
    assert_eq!(closure.locals[4].name.as_deref(), Some("y"));
}

#[test]
fn a_local_that_borrows_in_the_body_owns_its_value_in_the_caller() {
    // What it borrowed from outlived the body's call, and may not outlive the body.
    let mut g = callee(false);
    g.locals[2].borrowed = true;
    let f = spliced(caller(false), &g, true);
    assert!(!f.locals[4].borrowed);
}

#[test]
fn a_parameter_in_memory_takes_a_copy_of_its_argument() {
    let mut g = callee(false);
    g.locals[1].slot = true;
    let f = spliced(caller(false), &g, true);
    // `x` is the caller's `_4`, a copy of `_1` made before the body runs.
    assert_eq!(
        f.blocks[0].stmts.last(),
        Some(&assign(4, Rvalue::Use(op(1))))
    );
    assert!(f.locals[4].slot);
}

#[test]
fn a_call_whose_result_is_also_an_argument_is_left_as_it_is() {
    let mut f = caller(false);
    let g = callee(false);
    let body = Body {
        function: &g,
        args: vec![LOC, op(2)],
        std: true,
    };
    assert!(!splice(&mut f, BlockId(0), &body));
    assert_eq!(f, caller(false));
}

#[test]
fn a_generic_local_follows_the_local_that_stands_for_its_witness() {
    // `g<T>(w, x: T)`: the body's local of `T` is counted as the caller's witness `_1` says.
    let mut g = callee(false);
    g.locals[2].repr = Repr::Generic(Local(1));
    let f = spliced(caller(false), &g, true);
    assert_eq!(f.locals[4].repr, Repr::Generic(Local(1)));
    let mut constant = caller(false);
    let body = Body {
        function: &g,
        args: vec![LOC, Operand::word(9)],
        std: true,
    };
    // A constant can't stand for a witness, so the parameter takes a copy of it, `_4`.
    assert!(splice(&mut constant, BlockId(0), &body));
    assert_eq!(constant.locals[5].repr, Repr::Generic(Local(4)));
    assert_eq!(
        constant.blocks[0].stmts.last(),
        Some(&assign(4, Rvalue::Use(Operand::word(9))))
    );
}
