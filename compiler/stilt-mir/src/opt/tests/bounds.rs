//! A size that a branch bounds between constants bounds what is computed from it, so that a
//! product or a sum of such values loses its overflow check, as a grid's index `y * n + x` does
//! below a side that the program checked; without the branch every check stays.

use super::{branch, function, goto, op, optimized, prim, ret};
use crate::mir::{NumKind, Operand, ParamMode, Prim, Rvalue};

/// `if n <= limit { _4 = n * n; _5 = _4 + n }`, of the parameter `n`, `_1`, or the same without
/// the branch when `limit` is `None`.
fn squared(limit: Option<i64>) -> crate::mir::Function {
    let product = vec![
        prim(4, Prim::Mul(NumKind::I64), &[op(1), op(1)]),
        prim(5, Prim::Add(NumKind::I64), &[op(4), op(1)]),
    ];
    let blocks = match limit {
        Some(k) => vec![
            branch(
                vec![prim(2, Prim::Le(NumKind::I64), &[Operand::word(0), op(1)])],
                2,
                1,
                3,
            ),
            branch(
                vec![prim(
                    3,
                    Prim::Le(NumKind::I64),
                    &[op(1), Operand::word(k.cast_unsigned())],
                )],
                3,
                2,
                3,
            ),
            goto(product, 3),
            ret(Vec::new()),
        ],
        None => vec![goto(product, 1), ret(Vec::new())],
    };
    function(&[ParamMode::Borrowed], 5, &[], blocks)
}

#[test]
fn a_product_of_bounded_sizes_needs_no_overflow_check() {
    let f = squared(Some(1 << 20));
    let wrapped = |d, p| {
        optimized(f.clone(), d)
            .into_iter()
            .any(|r| matches!(r, Rvalue::Prim(q, ..) if q == p))
    };
    assert!(
        wrapped(4, Prim::MulWrap(NumKind::I64)),
        "{:?}",
        optimized(f.clone(), 4)
    );
    assert!(
        wrapped(5, Prim::AddWrap(NumKind::I64)),
        "{:?}",
        optimized(f.clone(), 5)
    );
}

#[test]
fn a_product_too_large_or_unbounded_keeps_its_check() {
    for limit in [Some(1 << 32), None] {
        let product = optimized(squared(limit), 4);
        assert!(
            matches!(product[0], Rvalue::Prim(Prim::Mul(NumKind::I64), ..)),
            "{limit:?}: {product:?}"
        );
    }
}
