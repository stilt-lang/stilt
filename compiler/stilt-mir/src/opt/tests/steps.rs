//! Steps taken without a branch: `if c { x += k }` steps `x` by `c * k`, with the step's check and
//! location, so it overflows only where the branch's step did (numbers.integer-panics). A branch
//! around anything else stays.

use super::{LOC, assign, branch, function, goto, op, optimized, prim, ret};
use crate::mir::{
    BlockId, Function, NumKind, Operand, ParamMode, Prim, Repr, Rvalue, Stmt, Terminator,
};

const I64: NumKind = NumKind::I64;

/// `var x = 0; if c { x += k }`, `c` being the parameter `_1` and `x` the local `_2`: block 1
/// copies `x` into `_3`, steps it into `_4` and copies it back, block 2 goes the other way,
/// both give the `if` its value `()` in `_5`, and block 3 returns. `then` and `otherwise` are
/// added to the end of blocks 1 and 2.
fn counting(k: u64, then: Vec<Stmt>, otherwise: Vec<Stmt>) -> Function {
    let unit = assign(5, Rvalue::Use(Operand::word(0)));
    let mut step = vec![
        assign(3, Rvalue::Use(op(2))),
        prim(4, Prim::Add(I64), &[op(3), Operand::word(k)]),
        assign(2, Rvalue::Use(op(4))),
        unit.clone(),
    ];
    step.extend(then);
    let mut other = vec![unit];
    other.extend(otherwise);
    let blocks = vec![
        branch(vec![assign(2, Rvalue::Use(Operand::word(0)))], 1, 1, 2),
        goto(step, 3),
        goto(other, 3),
        ret(Vec::new()),
    ];
    function(&[ParamMode::Borrowed], 5, &[], blocks)
}

/// Whether block 0 still branches once `f` is optimized.
fn stays(mut f: Function) -> bool {
    super::super::optimize(&mut f);
    matches!(f.blocks[0].term, Terminator::Branch { .. })
}

fn rvalue(p: Prim, args: &[Operand]) -> Rvalue {
    Rvalue::Prim(p, args.to_vec(), LOC)
}

#[test]
fn a_branch_around_a_step_by_1_steps_by_the_condition() {
    let f = counting(1, Vec::new(), Vec::new());
    assert_eq!(
        optimized(f.clone(), 4),
        [rvalue(Prim::Add(I64), &[op(3), op(1)])]
    );
    let mut g = f;
    super::super::optimize(&mut g);
    assert_eq!(g.blocks.len(), 2);
    assert_eq!(g.blocks[0].term, Terminator::Goto(BlockId(1)));
}

#[test]
fn a_branch_around_a_step_by_a_constant_steps_by_the_condition_times_it() {
    let f = counting(5, Vec::new(), Vec::new());
    let times = Rvalue::Prim(
        Prim::MulWrap(I64),
        vec![op(1), Operand::word(5)],
        Operand::word(0),
    );
    assert_eq!(optimized(f.clone(), 7), [times]);
    assert_eq!(optimized(f, 4), [rvalue(Prim::Add(I64), &[op(3), op(7)])]);
}

#[test]
fn a_branch_around_a_step_whose_temporary_is_read_later_stays() {
    // Block 3 reads `_4`, which holds the step only where `c` held.
    let mut f = counting(1, Vec::new(), Vec::new());
    f.blocks[3].term = Terminator::Return(vec![op(4)]);
    assert!(stays(f));
}

#[test]
fn a_branch_around_a_step_and_a_store_stays() {
    let store = Stmt::Store {
        slot: op(3),
        value: Operand::word(0),
        repr: Repr::Scalar,
    };
    assert!(stays(counting(1, vec![store], Vec::new())));
}

#[test]
fn a_branch_whose_other_way_does_something_else_stays() {
    let other = assign(2, Rvalue::Use(Operand::word(7)));
    assert!(stays(counting(1, Vec::new(), vec![other])));
}

#[test]
fn a_branch_around_two_steps_stays() {
    let again = prim(6, Prim::Add(I64), &[op(2), Operand::word(1)]);
    let f = counting(1, vec![again, assign(2, Rvalue::Use(op(6)))], Vec::new());
    assert!(stays(f));
}
