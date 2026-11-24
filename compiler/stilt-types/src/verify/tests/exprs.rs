//! Expressions (facts.terms, facts.linear-forms, facts.paths-that-leave and
//! facts.writes-through-calls): the values of constants, value parameters and negations, the
//! paths that `return`, `raise`, `break` and `continue` end, a call through a function value,
//! and the bodies of closures and operations, each analysed on its own.

use super::{checks, has, unproved};

/// A program of `items` and a function `f`, whose body starts with `three`, a list of three
/// elements, on the line after the function's: line 5 for items of one line.
fn with_items(items: &str, signature: &str, body: &str) -> String {
    format!(
        "module main\nuse std.array\n{items}\nfn f{signature} {{\n  let three = [0, 0, 0]\n{body}\n}}\n"
    )
}

#[test]
fn constants_and_negated_literals_have_their_values() {
    let text = with_items(
        "const TWO: i64 = 2",
        "(k: i64) -> i64",
        "  let a = three[TWO]\n  let b = three[i64.MAX - 9223372036854775805]\n  \
         let c = if k == -1 { three[k + 3] } else { 0 }\n  a + b + c",
    );
    let found = checks(&text, "f");
    has(&found, "6:11 bounds");
    has(&found, "7:11 bounds");
    has(&found, "8:24 bounds");
}

#[test]
fn a_value_parameter_and_a_negation_have_their_terms_and_intervals() {
    let text = with_items(
        "",
        "<n: i64>(v: array.Array<i64, n>, k: i64) -> i64",
        "  let a = if n >= 1 { v[n - 1] } else { 0 }\n  \
         let b = if k >= -2 && k <= 0 { three[-k] } else { 0 }\n  a + b",
    );
    let found = checks(&text, "f");
    has(&found, "6:23 bounds");
    has(&found, "7:34 bounds");
}

#[test]
fn a_path_that_returns_or_raises_takes_no_part_after() {
    let text = with_items(
        "type Bad = { k: i64 }",
        "(k: i64, j: i64) -> i64 / raise<Bad>",
        "  if k < 0 || k > 2 { return 0 }\n  if j < 0 || j > 2 { raise Bad { k: j } }\n  three[k] + three[j]",
    );
    let found = checks(&text, "f");
    has(&found, "8:3 bounds");
    has(&found, "8:14 bounds");
}

#[test]
fn break_and_continue_end_their_paths() {
    let text = with_items(
        "",
        "(n: i64) -> i64",
        "  var s = 0\n  var i = 0\n  loop {\n    if i >= 3 { break }\n    s += three[i]\n    i += 1\n  }\n  \
         for j in 0..n {\n    if j > 2 { continue }\n    s += three[j]\n  }\n  s",
    );
    let found = checks(&text, "f");
    has(&found, "10:10 bounds");
    has(&found, "15:10 bounds");
}

#[test]
fn a_call_through_a_function_value_writes_its_inout_arguments() {
    let text = with_items(
        "",
        "(g: fn(inout List<i64>)) -> i64",
        "  var xs = [1, 2, 3]\n  g(inout xs)\n  xs[2]",
    );
    has(&checks(&text, "f"), "8:3 no bounds");
}

#[test]
fn closures_and_operations_are_bodies_of_their_own() {
    let text = with_items(
        "effect Ask {\n  fn ask(j: i64) -> i64\n}",
        "(k: i64) -> i64",
        "  let g = |j: i64| three[j]\n  let h = handler Ask -> i64 {\n    fn ask(j: i64) -> i64 { resume(three[j]) }\n  }\n  \
         with h { g(k) + Ask.ask(k) }",
    );
    assert_eq!(unproved(&text), ["8:20 no bounds", "10:36 no bounds"]);
}

#[test]
fn if_let_and_else_keep_their_paths() {
    // `if let 2 = k` gives `k = 2` in its block, and the code after it meets both paths; the
    // fallback of `else` runs on a path of its own, which its assignment changes.
    let text = with_items(
        "",
        "(k: i64, o: Option<i64>) -> i64",
        "  let a = if let 2 = k { three[k] } else { 0 }\n  var i = 0\n  let b = o else { i = 5\n    0 }\n  \
         a + b + three[k] + three[i]",
    );
    let found = checks(&text, "f");
    has(&found, "6:26 bounds");
    has(&found, "10:11 no bounds");
    has(&found, "10:22 no bounds");
}
