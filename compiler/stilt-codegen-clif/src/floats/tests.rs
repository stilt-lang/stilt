use cranelift_codegen::ir::types::{F64, I64};
use stilt_mir::mir::{NumKind, Operand, Prim, Rvalue, Stmt, Terminator};

use super::local_types;
use crate::debug::Place;
use crate::target::Target;
use crate::testing::{
    block, clif, clif_blocks, facts, float_loop, function, heap, local, named_f64, op, prim, scalar,
};

#[test]
fn the_locals_of_a_float_loop_hold_f64s_and_its_counters_words() {
    assert_eq!(
        local_types(&float_loop()),
        [I64, I64, F64, I64, I64, F64, F64, I64]
    );
}

#[test]
fn a_float_loop_moves_no_value_between_integer_and_float_registers() {
    let clif = clif(&float_loop());
    let blocks = clif_blocks(&clif);
    assert!(
        blocks.iter().any(|b| b.has("fmul") && b.has("fadd")),
        "{clif}"
    );
    // The one bitcast is the result's, which the calling convention returns as a word.
    let bitcasts: Vec<_> = blocks.iter().filter(|b| b.has("bitcast")).collect();
    assert_eq!(bitcasts.len(), 1, "{clif}");
    assert_eq!(bitcasts[0].ends_in(), "return", "{clif}");
}

/// `_2 = _1.0`, `_3 = _2`, `_4 = -_3`, `_5 = _1`, return `_4`.
fn copies() -> stilt_mir::mir::Function {
    let field = Rvalue::Field {
        base: op(1),
        len: 1,
        index: 0,
        variant: None,
    };
    let stmts = vec![
        Stmt::Assign(local(2), field),
        Stmt::Assign(local(3), Rvalue::Use(op(2))),
        prim(4, Prim::Neg(NumKind::F64), &[op(3)]),
        Stmt::Assign(local(5), Rvalue::Use(op(1))),
    ];
    let blocks = vec![block(stmts, Terminator::Return(vec![op(4)]))];
    function(&[heap()], &[scalar(), scalar(), scalar(), heap()], blocks)
}

#[test]
fn a_copy_joins_two_locals_into_one_type_and_memory_gives_floats_as_they_are() {
    let f = copies();
    assert_eq!(local_types(&f), [I64, I64, F64, F64, F64, I64]);
    let clif = clif(&f);
    assert!(clif.contains("load.f64"), "{clif}");
    assert_eq!(clif.matches("bitcast").count(), 1, "{clif}");
}

#[test]
fn a_float_in_a_register_shows_by_the_register_s_dwarf_number() {
    // `x = n.to_f64()`, return `x * x`.
    let stmts = vec![
        prim(2, Prim::ToFloat(NumKind::I64, NumKind::F64), &[op(1)]),
        prim(3, Prim::Mul(NumKind::F64), &[op(2), op(2)]),
    ];
    let f = function(
        &[scalar()],
        &[named_f64("x"), scalar()],
        vec![block(stmts, Terminator::Return(vec![op(3)]))],
    );
    // v0 to v31 on aarch64, and xmm0 to xmm15 on x86-64.
    for (target, floats) in [
        (Target::Aarch64Macos, 64..=95),
        (Target::X86_64Linux, 17..=32),
    ] {
        let facts = facts(&f, target);
        let x = facts.vars.iter().find(|v| &*v.name == "x").expect("x");
        assert!(
            x.ranges
                .iter()
                .any(|&(_, _, place)| matches!(place, Place::Reg(r) if floats.contains(&r))),
            "{target}: {:?}",
            x.ranges
        );
    }
}

#[test]
fn a_float_constant_is_a_float_of_its_bits() {
    let stmts = vec![Stmt::Assign(
        local(1),
        Rvalue::Use(Operand::word(crate::testing::ONE_AND_A_HALF)),
    )];
    let f = function(
        &[],
        &[named_f64("ratio")],
        vec![block(stmts, Terminator::Return(vec![op(1)]))],
    );
    let clif = clif(&f);
    assert!(clif.contains("f64const 0x1.8000000000000p0"), "{clif}");
}
