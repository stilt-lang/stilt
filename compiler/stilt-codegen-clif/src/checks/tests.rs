//! The cheaper checks of a constant operand and of a division's overflow, which still panic
//! wherever the operation can fail.

use stilt_mir::mir::{NumKind, Operand, Prim, Terminator};

use crate::testing::{block, clif, clif_blocks, function, op, prim, scalar};

/// The Cranelift IR of a function that returns `p` of its parameters `_1` and `_2` and the
/// operands `args`.
fn clif_of(p: Prim, args: &[Operand]) -> String {
    let f = function(
        &[scalar(), scalar()],
        &[scalar()],
        vec![block(
            vec![prim(3, p, args)],
            Terminator::Return(vec![op(3)]),
        )],
    );
    clif(&f)
}

/// The opcodes of the hot blocks, and of the cold ones, in order.
fn opcodes(clif: &str, cold: bool) -> Vec<String> {
    clif_blocks(clif)
        .iter()
        .filter(|b| b.cold() == cold)
        .flat_map(|b| b.insts.iter())
        .map(|i| {
            let rhs = i.split_once(" = ").map_or(*i, |(_, r)| r);
            let word = rhs.split_whitespace().next().unwrap_or("");
            word.split('.').next().unwrap_or("").to_owned()
        })
        .collect()
}

/// How many cold blocks call the runtime, which only a failed check does here.
fn panics(clif: &str) -> usize {
    clif_blocks(clif)
        .iter()
        .filter(|b| b.cold() && b.has("call"))
        .count()
}

#[test]
fn adding_a_constant_compares_with_a_bound_instead_of_flagging_an_overflow() {
    let clif = clif_of(Prim::Add(NumKind::I64), &[op(1), Operand::word(1)]);
    let hot = opcodes(&clif, false);
    assert!(clif.contains("icmp.i64 sgt v5, v6"), "{clif}");
    assert!(!hot.contains(&"sadd_overflow".to_owned()), "{clif}");
    assert_eq!(panics(&clif), 1, "{clif}");
}

#[test]
fn subtracting_a_constant_from_an_unsigned_integer_still_panics() {
    let clif = clif_of(Prim::Sub(NumKind::U8), &[op(1), Operand::word(3)]);
    assert!(clif.contains("icmp.i64 ult v5, v6"), "{clif}");
    assert_eq!(panics(&clif), 1, "{clif}");
}

#[test]
fn adding_zero_checks_nothing() {
    let clif = clif_of(Prim::Add(NumKind::I64), &[Operand::word(0), op(1)]);
    assert_eq!(panics(&clif), 0, "{clif}");
}

#[test]
fn adding_two_variables_keeps_the_overflow_flag() {
    let clif = clif_of(Prim::Add(NumKind::I64), &[op(1), op(2)]);
    assert!(opcodes(&clif, false).contains(&"sadd_overflow".to_owned()));
    assert_eq!(panics(&clif), 1, "{clif}");
}

#[test]
fn a_division_by_a_constant_other_than_zero_and_minus_one_checks_nothing() {
    let clif = clif_of(Prim::Div(NumKind::I64), &[op(1), Operand::word(2)]);
    assert_eq!(panics(&clif), 0, "{clif}");
}

#[test]
fn a_division_by_minus_one_or_zero_keeps_what_can_fail() {
    let minus_one = Operand::word(u64::MAX);
    let clif = clif_of(Prim::Rem(NumKind::I64), &[op(1), minus_one]);
    assert_eq!(panics(&clif), 1, "{clif}");
    // By 0: the division by zero, and the overflow that a variable divisor checks.
    let clif = clif_of(Prim::Div(NumKind::I64), &[op(1), Operand::word(0)]);
    assert_eq!(panics(&clif), 2, "{clif}");
}

#[test]
fn a_division_by_a_variable_tests_the_least_value_only_off_the_hot_path() {
    let clif = clif_of(Prim::Div(NumKind::I32), &[op(1), op(2)]);
    let hot = opcodes(&clif, false);
    // The divisor against 0 and -1; the dividend against the least `i32` only when cold.
    assert_eq!(hot.iter().filter(|o| *o == "icmp").count(), 2, "{clif}");
    assert!(!hot.contains(&"band".to_owned()), "{clif}");
    let cold = opcodes(&clif, true);
    assert_eq!(cold.iter().filter(|o| *o == "icmp").count(), 1, "{clif}");
    assert!(clif.contains("iconst.i64 -2147483648"), "{clif}");
    assert_eq!(panics(&clif), 2, "{clif}");
}

#[test]
fn an_addition_of_terms_at_least_zero_tests_only_the_sign_of_its_sum() {
    let clif = clif_of(Prim::AddUp(NumKind::I64), &[op(1), op(2)]);
    let hot = opcodes(&clif, false);
    assert!(!hot.contains(&"sadd_overflow".to_owned()), "{clif}");
    assert!(hot.contains(&"band".to_owned()), "{clif}");
    assert_eq!(panics(&clif), 1, "{clif}");
}

#[test]
fn a_division_by_a_divisor_proved_positive_checks_nothing() {
    for p in [
        Prim::DivByPositive(NumKind::I64),
        Prim::RemByPositive(NumKind::I64),
    ] {
        let clif = clif_of(p, &[op(1), op(2)]);
        assert!(
            !opcodes(&clif, false).contains(&"icmp".to_owned()),
            "{clif}"
        );
        assert_eq!(panics(&clif), 0, "{clif}");
    }
}
