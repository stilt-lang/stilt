//! The checks of arithmetic that the range facts discharge or make cheaper: a division by a
//! divisor known positive, an addition of terms at least 0, which can only overflow upward,
//! and a subtraction of 1 from a term above 0; and the facts that find them: a copy equal to
//! its source, a sum with a term above 0, and an element of a `bool` list. Each check that can
//! fail is kept (numbers.integer-panics).

use super::{LOC, assign, counted_loop, function, goto, index, op, optimized, prim, ret};
use crate::mir::{BlockId, NumKind, Operand, ParamMode, Prim, Runtime, Rvalue, Stmt, Terminator};

const I64: NumKind = NumKind::I64;

/// `counted_loop` whose body, block 3, runs `body` before the counter's step, with `extra`
/// more scalar locals from `_7`.
fn looping(body: Vec<Stmt>, extra: usize) -> crate::mir::Function {
    let mut f = counted_loop(1, Rvalue::Use(Operand::word(0)));
    f.locals
        .extend((0..extra).map(|_| super::decl(crate::mir::Repr::Scalar, false)));
    let step = f.blocks[3].stmts.pop().expect("the step");
    f.blocks[3].stmts = body;
    f.blocks[3].stmts.push(step);
    f
}

fn rvalue(p: Prim, args: &[Operand]) -> Rvalue {
    Rvalue::Prim(p, args.to_vec(), LOC)
}

#[test]
fn a_remainder_by_a_loops_bound_inside_the_loop_checks_nothing() {
    // `i % n` where `0 <= i < n`, so `n` is above 0.
    let f = looping(vec![prim(7, Prim::Rem(I64), &[op(4), op(3)])], 1);
    assert_eq!(
        optimized(f, 7),
        [rvalue(Prim::RemByPositive(I64), &[op(4), op(3)])]
    );
}

#[test]
fn a_division_by_a_bound_that_may_be_zero_keeps_its_check() {
    // `i / n` before the loop, where `n` may be 0.
    let mut f = looping(Vec::new(), 1);
    f.blocks[1]
        .stmts
        .push(prim(7, Prim::Div(I64), &[op(4), op(3)]));
    assert_eq!(optimized(f, 7), [rvalue(Prim::Div(I64), &[op(4), op(3)])]);
}

#[test]
fn a_sum_of_terms_at_least_0_can_only_overflow_upward() {
    // `i + i` may overflow, but only past the maximum.
    let f = looping(vec![prim(7, Prim::Add(I64), &[op(4), op(4)])], 1);
    assert_eq!(optimized(f, 7), [rvalue(Prim::AddUp(I64), &[op(4), op(4)])]);
}

#[test]
fn one_less_than_a_sum_with_a_term_above_0_is_at_least_0() {
    // `(i + n - 1) + i`: `i + n` is above 0, as `n` is, so `i + n - 1` is at least 0.
    let body = vec![
        prim(7, Prim::Add(I64), &[op(4), op(3)]),
        prim(8, Prim::Sub(I64), &[op(7), Operand::word(1)]),
        prim(9, Prim::Add(I64), &[op(8), op(4)]),
    ];
    let f = looping(body, 3);
    assert_eq!(
        optimized(f.clone(), 8),
        [rvalue(Prim::SubWrap(I64), &[op(7), Operand::word(1)])]
    );
    assert_eq!(optimized(f, 9), [rvalue(Prim::AddUp(I64), &[op(8), op(4)])]);
}

#[test]
fn an_element_of_a_bool_list_is_at_least_0() {
    // `i + flags[i]`, the element read as a byte that its read doesn't extend the sign of.
    let byte = Operand::word(crate::shape::packed(1, false));
    let read = Rvalue::Runtime(Runtime::ListAt, vec![op(1), op(4), byte, Operand::word(0)]);
    let body = vec![assign(7, read), prim(8, Prim::Add(I64), &[op(4), op(7)])];
    let f = looping(body, 2);
    assert_eq!(optimized(f, 8), [rvalue(Prim::AddUp(I64), &[op(4), op(7)])]);
}

#[test]
fn an_index_read_through_one_copy_is_in_bounds_through_another() {
    // `xs[k]` twice, `k` being the parameter `_2`, each time through a copy of its own.
    let blocks = vec![ret(vec![
        assign(3, Rvalue::Use(op(2))),
        assign(4, index(1, op(3))),
        assign(5, Rvalue::Use(op(2))),
        assign(6, index(1, op(5))),
    ])];
    let f = function(&[ParamMode::Borrowed, ParamMode::Borrowed], 4, &[1], blocks);
    let at = Rvalue::Runtime(
        Runtime::ListAt,
        vec![op(1), op(5), super::SHAPE, Operand::word(0)],
    );
    assert_eq!(optimized(f.clone(), 4), [index(1, op(3))]);
    assert_eq!(optimized(f, 6), [at]);
}

#[test]
fn the_test_that_ends_an_iteration_of_a_counted_loop_is_decided() {
    // `for i in 0..n` tests `i < n` again before its step, in block 5, which jumps to the step
    // in block 6: the loop's test has held, and neither has changed.
    let mut f = looping(Vec::new(), 1);
    let step = f.blocks[3].stmts.pop().expect("the step");
    f.blocks[3].term = Terminator::Goto(BlockId(5));
    f.blocks.push(super::branch(
        vec![prim(7, Prim::Lt(I64), &[op(4), op(3)])],
        7,
        6,
        4,
    ));
    f.blocks.push(goto(vec![step], 2));
    let mut g = f;
    super::super::optimize(&mut g);
    assert_eq!(g.blocks[5].term, Terminator::Goto(BlockId(6)));
}
