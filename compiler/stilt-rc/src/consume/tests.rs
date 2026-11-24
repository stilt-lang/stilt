//! What a summary finds a body consuming, and what the fixed point and the conventions make of
//! it (values.consumed-parameters).

use stilt_hir::hir::{Item, Name};
use stilt_mir::FnRef;
use stilt_mir::mir::{
    Arg, Block, BlockId, Callee, Function, Local, LocalDecl, Operand, Param, ParamMode, Repr,
    Rvalue, Stmt, Terminator,
};

use super::{Conventions, Summary, apply, summary};
use crate::fixpoint::{components, solve};

fn item(name: &str) -> FnRef {
    FnRef::Function(Item {
        home: Name::from("main"),
        name: Name::from(name),
    })
}

fn decl(repr: Repr) -> LocalDecl {
    LocalDecl {
        repr,
        slot: false,
        grouped: false,
        borrowed: false,
        var: false,
        name: None,
        shown: None,
    }
}

/// A function of one block, whose first local is its location and whose next `heap` locals are
/// heap parameters, with `extra` more heap locals.
fn function(heap: u32, extra: u32, stmts: Vec<Stmt>, term: Terminator) -> Function {
    let mut locals = vec![decl(Repr::Scalar)];
    locals.extend((0..heap + extra).map(|_| decl(Repr::Heap)));
    let params = (0..=heap)
        .map(|i| Param {
            local: Local(i),
            mode: ParamMode::Borrowed,
        })
        .collect();
    Function {
        name: item("f"),
        params,
        hidden: 1,
        results: 1,
        locals,
        blocks: vec![Block { stmts, term }],
        broken: false,
    }
}

fn local(i: u32) -> Operand {
    Operand::Local(Local(i))
}

fn call(g: &str, args: Vec<Arg>, dest: u32) -> Terminator {
    Terminator::Call {
        callee: Callee::Direct(item(g)),
        args,
        dest: vec![Local(dest)],
        next: BlockId(0),
        raised: None,
    }
}

#[test]
fn a_returned_parameter_is_consumed_and_a_read_one_is_not() {
    let f = function(
        2,
        1,
        vec![Stmt::Assign(Local(3), Rvalue::Tag(local(2)))],
        Terminator::Return(vec![local(1)]),
    );
    assert_eq!(summary(&f).consumed, [1]);
}

#[test]
fn a_parameter_stored_in_a_value_is_consumed() {
    let alloc = Rvalue::Alloc(0, vec![(local(1), stilt_mir::mir::Heapness::Static(true))]);
    let f = function(
        1,
        1,
        vec![Stmt::Assign(Local(2), alloc)],
        Terminator::Return(vec![local(2)]),
    );
    assert_eq!(summary(&f).consumed, [1]);
}

#[test]
fn a_let_copy_stands_for_its_parameter() {
    // `let y = x` then a read of `y` consumes nothing; returning `y` consumes `x`.
    let read = function(
        1,
        2,
        vec![
            Stmt::Assign(Local(2), Rvalue::Use(local(1))),
            Stmt::Assign(Local(3), Rvalue::Tag(local(2))),
        ],
        Terminator::Return(vec![local(3)]),
    );
    assert_eq!(summary(&read).consumed, Vec::<usize>::new());
    let returned = function(
        1,
        1,
        vec![Stmt::Assign(Local(2), Rvalue::Use(local(1)))],
        Terminator::Return(vec![local(2)]),
    );
    assert_eq!(summary(&returned).consumed, [1]);
}

#[test]
fn a_var_copy_consumes_its_parameter_even_unchanged() {
    // values.consumed-parameters: `var y = x` consumes `x`, though the code only reads `y`.
    let mut f = function(
        1,
        2,
        vec![
            Stmt::Assign(Local(2), Rvalue::Use(local(1))),
            Stmt::Assign(Local(3), Rvalue::Tag(local(2))),
        ],
        Terminator::Return(vec![local(3)]),
    );
    f.locals[2].var = true;
    assert_eq!(summary(&f).consumed, [1]);
}

#[test]
fn a_variable_that_changes_consumes_its_parameter() {
    // `var y = x` that is assigned again, or that lives in memory, takes a reference.
    let twice = function(
        1,
        1,
        vec![
            Stmt::Assign(Local(2), Rvalue::Use(local(1))),
            Stmt::Assign(Local(2), Rvalue::Use(Operand::word(1))),
        ],
        Terminator::Return(vec![Operand::word(0)]),
    );
    assert_eq!(summary(&twice).consumed, [1]);
    let mut slot = function(
        1,
        1,
        vec![Stmt::Assign(Local(2), Rvalue::Use(local(1)))],
        Terminator::Return(vec![Operand::word(0)]),
    );
    slot.locals[2].slot = true;
    assert_eq!(summary(&slot).consumed, [1]);
}

#[test]
fn a_parameter_passed_on_waits_for_its_callee() {
    let f = function(
        1,
        1,
        Vec::new(),
        call(
            "g",
            vec![Arg::Borrow(Operand::word(0)), Arg::Borrow(local(1))],
            2,
        ),
    );
    assert_eq!(
        summary(&f),
        Summary {
            consumed: Vec::new(),
            passed: vec![(1, item("g"), 1)],
        }
    );
}

#[test]
fn consumption_flows_back_through_calls_and_recursion() {
    let take = Summary {
        consumed: vec![1],
        passed: Vec::new(),
    };
    let pass = Summary {
        consumed: Vec::new(),
        passed: vec![(1, item("take"), 1)],
    };
    // `even` and `odd` pass their parameter to each other, and `odd` also to `pass`.
    let even = Summary {
        consumed: Vec::new(),
        passed: vec![(1, item("odd"), 1)],
    };
    let odd = Summary {
        consumed: Vec::new(),
        passed: vec![(1, item("even"), 1), (1, item("pass"), 1)],
    };
    let lone = Summary {
        consumed: Vec::new(),
        passed: vec![(1, item("lone"), 1), (1, item("native"), 1)],
    };
    let all = [
        (item("even"), &even),
        (item("odd"), &odd),
        (item("pass"), &pass),
        (item("take"), &take),
        (item("lone"), &lone),
    ];
    let solved = solve(&all);
    for name in ["even", "odd", "pass", "take"] {
        assert_eq!(solved[&item(name)], [1], "{name}");
    }
    assert_eq!(solved[&item("lone")], Vec::<usize>::new());
}

#[test]
fn components_come_after_those_they_reach() {
    // 0 -> 1 <-> 2 -> 3, and 4 alone.
    let edges = vec![vec![1], vec![2], vec![1, 3], vec![], vec![]];
    let found = components(&edges);
    let place = |n: usize| {
        found
            .iter()
            .position(|c| c.contains(&n))
            .expect("every node")
    };
    assert_eq!(place(1), place(2));
    assert!(place(3) < place(1));
    assert!(place(1) < place(0));
    assert_eq!(found.len(), 4);
}

#[test]
fn conventions_own_what_is_consumed() {
    let mut f = function(
        2,
        1,
        Vec::new(),
        call(
            "g",
            vec![
                Arg::Borrow(Operand::word(0)),
                Arg::Borrow(local(1)),
                Arg::Ref(local(2)),
            ],
            3,
        ),
    );
    apply(
        &mut f,
        &Conventions {
            owned: vec![2],
            calls: vec![vec![1, 2]],
            unique: Vec::new(),
        },
    );
    let modes: Vec<ParamMode> = f.params.iter().map(|p| p.mode).collect();
    assert_eq!(
        modes,
        [ParamMode::Borrowed, ParamMode::Borrowed, ParamMode::Owned]
    );
    let Terminator::Call { args, .. } = &f.blocks[0].term else {
        unreachable!("a call")
    };
    assert_eq!(args[1], Arg::Own(local(1)));
    // An `inout` argument stays a pointer, whatever the callee consumes.
    assert_eq!(args[2], Arg::Ref(local(2)));
}
