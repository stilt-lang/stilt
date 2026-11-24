//! Divisions and remainders (facts.proved-divisions, facts.proved-overflow, facts.intervals and
//! facts.relative-bounds): which divisors are proved non-zero, which signed divisions can't
//! overflow, the intervals of quotients and remainders, and the middle of two forms.

use super::{has, verdicts};

/// A program of one function `f`, whose body starts on line 4.
fn function(signature: &str, body: &str) -> String {
    format!("module main\nuse std.array\nfn f{signature} {{\n{body}\n}}\n")
}

#[test]
fn a_divisor_and_a_dividend_each_rule_out_an_overflow() {
    // `MIN / -1` overflows: a dividend that can't be MIN, or a divisor that can't be −1, proves
    // the division. A divisor of at least 1 gives the quotient and the remainder intervals.
    let body = "  if a >= 0 && a <= 100 && b >= 10 && b <= 20 && e >= 1 && e <= 5 && d >= -5 && d <= 5 {\n    \
                let eleven = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]\n    let twenty = List.repeat(0, 20)\n    \
                let q1 = eleven[a / b]\n    let q2 = twenty[a % b]\n    let q3 = c / e\n    \
                let q4 = a / c\n    let q5 = eleven[a / d]\n    q1 + q2 + q3 + q4 + q5\n  } else { 0 }";
    let found = verdicts(
        &function("(a: i64, b: i64, c: i64, d: i64, e: i64) -> i64", body),
        "f",
    );
    has(&found, "7:14 bounds");
    has(&found, "7:21 divide-by-zero");
    has(&found, "7:21 overflow");
    has(&found, "8:14 bounds");
    has(&found, "9:14 divide-by-zero");
    has(&found, "9:14 overflow");
    has(&found, "10:14 no divide-by-zero");
    has(&found, "10:14 overflow");
    // A divisor that may be negative gives the quotient its type's bounds.
    has(&found, "11:14 no bounds");
    has(&found, "11:21 no divide-by-zero");
}

#[test]
fn an_unsigned_division_never_overflows() {
    let found = verdicts(
        &function(
            "(a: u64, b: u64) -> u64",
            "  if b >= 1 { a / b } else { 0 }",
        ),
        "f",
    );
    has(&found, "4:15 divide-by-zero");
    assert!(!found.iter().any(|v| v.ends_with("overflow")), "{found:#?}");
}

#[test]
fn a_remainder_is_less_than_its_divisor() {
    let body = "  if a >= 0 && xs.len() > 0 {\n    xs[a % xs.len()]\n  } else { 0 }";
    let found = verdicts(&function("(xs: List<i64>, a: i64) -> i64", body), "f");
    has(&found, "5:5 bounds");
}

/// The verdict on `xs[mid]` under `cond`, with `mid` in place.
fn middle(cond: &str, mid: &str) -> Vec<String> {
    let body = format!("  if {cond} {{\n    xs[{mid}]\n  }} else {{ 0 }}");
    verdicts(
        &function("(xs: List<i64>, i: i64, j: i64) -> i64", &body),
        "f",
    )
}

#[test]
fn the_middle_of_two_forms_lies_between_them() {
    // `(a + b) / 2` with `a ≤ b`: at least `a`, and below `b` when `a < b`.
    let mid = "(i + 2 + j) / 2";
    has(
        &middle("i >= 0 && i + 2 < j && j <= xs.len()", mid),
        "5:5 bounds",
    );
    // With `i + 2 = j = ℓ` the middle is `ℓ`.
    has(
        &middle("i >= 0 && i + 2 <= j && j <= xs.len()", mid),
        "5:5 no bounds",
    );
    // With only `i ≤ j`, `i + 2` may pass `j`: no relation holds.
    has(
        &middle("i >= 0 && i <= j && j < xs.len()", mid),
        "5:5 no bounds",
    );
}

#[test]
fn a_step_from_the_low_end_needs_a_divisor_of_at_least_2() {
    let cond = "i >= 0 && i < j && j <= xs.len()";
    has(&middle(cond, "i + (j - i) / 3"), "5:5 bounds");
    // Dividing by 1 reaches `j` itself.
    has(&middle(cond, "i + (j - i) / 1"), "5:5 no bounds");
}

#[test]
fn a_remainder_by_a_divisor_that_may_be_zero_has_no_relative_bound() {
    let body = "  if a >= 0 {\n    xs[a % xs.len()]\n  } else { 0 }";
    let found = verdicts(&function("(xs: List<i64>, a: i64) -> i64", body), "f");
    has(&found, "5:5 no bounds");
    has(&found, "5:8 no divide-by-zero");
}

#[test]
fn the_middle_is_at_least_the_low_end() {
    // With `0 ≤ i + 2 < j`, `(i + 2 + j) / 2` is at least `i + 2`, so the `else` is never
    // reached and its access is proved, however large `i` is.
    let body = "  if i >= -2 && i + 2 < j {\n    let mid = (i + 2 + j) / 2\n    \
                if mid >= i + 2 { 0 } else { xs[100] }\n  } else { 0 }";
    let found = verdicts(
        &function("(xs: List<i64>, i: i64, j: i64) -> i64", body),
        "f",
    );
    has(&found, "6:34 bounds");
}
