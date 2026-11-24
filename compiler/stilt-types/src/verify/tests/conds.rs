//! Conditions (facts.conditions): the facts where an order, an equality against 0, a
//! connective or `xs.is_empty()` is true, and where it is false.

use super::{checks, has};

/// The verdicts of `expr`, on line 6, where `cond` is true, or where it is false.
fn under(cond: &str, holds: bool, expr: &str) -> Vec<String> {
    let branch = if holds {
        format!("  if {cond} {{\n    {expr}\n  }} else {{ 0 }}")
    } else {
        format!("  if {cond} {{ 0 }} else {{\n    {expr}\n  }}")
    };
    let text = format!(
        "module main\n\nfn f(k: i64, j: i64, n: i64, xs: List<i64>) -> i64 {{\n  let three = [0, 0, 0]\n{branch}\n}}\n"
    );
    checks(&text, "f")
}

#[test]
fn orders_bound_their_operands_both_ways() {
    has(&under("3 > k && k >= 0", true, "three[k]"), "6:5 bounds");
    has(
        &under("k + 1 < 4 && k >= 0", true, "three[k]"),
        "6:5 bounds",
    );
    has(
        &under("k + 1 <= 4 && k >= 0", true, "three[k]"),
        "6:5 no bounds",
    );
    // Where `k >= 3` is false, `k < 3`, strictly.
    has(&under("k < 0 || k >= 3", false, "three[k]"), "6:5 bounds");
    has(&under("k < 0 || k > 3", false, "three[k]"), "6:5 no bounds");
}

#[test]
fn a_term_compared_with_zero_is_non_zero_where_they_differ() {
    has(&under("k != 0", true, "n / k"), "6:5 divide-by-zero");
    has(&under("0 != k", true, "n / k"), "6:5 divide-by-zero");
    has(&under("k == 0", false, "n / k"), "6:5 divide-by-zero");
    // `k + 1` differing from 0, or `k` from another binding, says nothing of `k`.
    has(&under("k + 1 != 0", true, "n / k"), "6:5 no divide-by-zero");
    has(&under("0 != k + 1", true, "n / k"), "6:5 no divide-by-zero");
    has(&under("j != k", true, "n / k"), "6:5 no divide-by-zero");
}

#[test]
fn an_empty_list_has_length_zero() {
    has(&under("xs.is_empty()", false, "xs[0]"), "6:5 bounds");
    has(&under("xs.is_empty()", true, "xs[0]"), "6:5 no bounds");
}
