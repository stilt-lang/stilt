//! A generic function of the standard library instantiated at a call whose witnesses are
//! constant: its words of a type parameter are counted as their shape says,
//! and it reads and appends its lists' elements as code that names their type does, a value of
//! several words still held in its box.

use super::{LOC, assign, function, op, ret};
use crate::mir::{Function, Heapness, Local, Operand, ParamMode, Repr, Runtime, Rvalue, Stmt};
use crate::opt::inline::instance::instantiate;
use crate::shape;

/// `g<T>(w, xs: List<T>, i)`: the witness `_1`, the list `_2`, the index `_3`, and the
/// statements `stmts`, whose local `_4` holds a value of `T`; the locals that instantiating
/// adds start at `_6`.
fn generic(stmts: Vec<Stmt>) -> Function {
    let mut g = function(
        &[
            ParamMode::Borrowed,
            ParamMode::Borrowed,
            ParamMode::Borrowed,
        ],
        2,
        &[2],
        vec![ret(stmts)],
    );
    g.locals[4].repr = Repr::Generic(Local(1));
    g
}

fn get() -> Stmt {
    assign(
        4,
        Rvalue::Runtime(Runtime::ListGet, vec![LOC, op(2), op(3), op(1)]),
    )
}

fn index(d: u32, s: u64, word: u64) -> Stmt {
    let args = vec![LOC, op(2), op(3), Operand::word(s), Operand::word(word)];
    assign(d, Rvalue::Runtime(Runtime::ListIndex, args))
}

fn instantiated(stmts: Vec<Stmt>, s: u64) -> Function {
    let mut g = generic(stmts);
    instantiate(&mut g, &[(Local(1), s)]);
    g
}

#[test]
fn a_read_of_an_element_of_one_word_reads_it_in_place() {
    let s = shape::word(true);
    let g = instantiated(vec![get()], s);
    assert_eq!(g.blocks[0].stmts, [index(4, s, 0)]);
    assert_eq!(g.locals[4].repr, Repr::Heap);
}

#[test]
fn a_read_of_an_element_of_several_words_is_left_to_the_runtime() {
    // A function that holds a value of a type parameter in one word is compiled for arguments
    // of one word, so it never meets one of several; the runtime would convert it.
    let s = shape::sized(&[false, true]);
    let g = instantiated(vec![get()], s);
    assert_eq!(g.blocks[0].stmts, [get()]);
}

#[test]
fn an_append_of_a_value_of_one_word_names_its_shape() {
    // A narrow scalar is one word where a type parameter stands, as in the code that names it.
    let s = shape::packed(1, false);
    let append = Stmt::Effect(Runtime::ListPush, vec![op(2), op(1), op(4)]);
    let g = instantiated(vec![append], s);
    let named = Stmt::Effect(Runtime::ListPush, vec![op(2), Operand::word(s), op(4)]);
    assert_eq!(g.blocks[0].stmts, [named]);
    assert_eq!(g.locals[4].repr, Repr::Scalar);
}

#[test]
fn a_field_of_a_type_parameter_is_counted_as_its_shape_says() {
    let alloc = assign(
        5,
        Rvalue::Alloc(0, vec![(op(4), Heapness::Witness(Local(1)))]),
    );
    let g = instantiated(vec![alloc], shape::word(true));
    let counted = assign(5, Rvalue::Alloc(0, vec![(op(4), Heapness::Static(true))]));
    assert_eq!(g.blocks[0].stmts, [counted]);
}

#[test]
fn a_witness_left_unknown_leaves_the_function_as_it_is() {
    let mut g = generic(vec![get()]);
    instantiate(&mut g, &[]);
    assert_eq!(g, generic(vec![get()]));
}
