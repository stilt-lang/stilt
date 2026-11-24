//! The forms that go elsewhere than to the next expression (facts.paths-that-leave and
//! facts.joins): `continue` to its loop's head, `raise` to a `catch`, `return` out of the body,
//! the fallback of an `else` only on `None`, and the body of a `loop` until its facts hold.

use super::{checks, has};

/// A program of one function `f`, whose body starts on line 4.
fn function(signature: &str, body: &str) -> String {
    format!("module main\nuse std.array\nfn f{signature} {{\n{body}\n}}\n")
}

#[test]
fn a_continue_joins_the_loop_head() {
    let body = |jump: &str| {
        format!(
            "  var xs = [1, 2, 3]\n  var j = 0\n  var n = 0\n  while n < 10 {{\n    n += 1\n    \
             let a = xs[j]\n    if k > 0 {{\n      j = 5\n{jump}    }}\n    j = 0\n    s(a)\n  }}\n  0"
        )
    };
    let text = |jump| function("(k: i64) -> i64", &body(jump)) + "fn s(a: i64) {}\n";
    // With `j = 5` at the head through the `continue`, `xs[j]` isn't proved; without it,
    // every path reaches the head with `j = 0`.
    has(&checks(&text("      continue\n"), "f"), "9:13 no bounds");
    has(&checks(&text(""), "f"), "9:13 bounds");
}

#[test]
fn a_raise_under_a_try_reaches_its_catch() {
    let body = "  var xs = [1, 2, 3]\n  var j = 0\n  let v = try {\n    if k > 0 {\n      j = 9\n      \
                raise \"x\"\n    }\n    1\n  } catch {\n    _ => xs[j]\n  }\n  v";
    has(
        &checks(&function("(k: i64) -> i64", body), "f"),
        "13:10 no bounds",
    );
}

#[test]
fn a_return_leaves_the_body() {
    let body = "  if k < 0 || k >= xs.len() { return 0 }\n  xs[k]";
    has(
        &checks(&function("(xs: List<i64>, k: i64) -> i64", body), "f"),
        "5:3 bounds",
    );
}

#[test]
fn an_else_runs_its_fallback_only_on_none() {
    // `j` is 0 or 9 after the `else`, so `j - 9` may be -9.
    let body = "  var xs = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]\n  var j = 0\n  let v = o else {\n    \
                j = 9\n    0\n  }\n  xs[j - 9] + v";
    has(
        &checks(&function("(o: Option<i64>) -> i64", body), "f"),
        "10:3 no bounds",
    );
}

#[test]
fn a_loop_runs_its_body_until_its_facts_hold() {
    let body = "  var xs = [1, 2, 3]\n  var j = 0\n  var s = 0\n  loop {\n    s += xs[j]\n    \
                j += 1\n    if j > 5 { break }\n  }\n  s";
    has(&checks(&function("() -> i64", body), "f"), "8:10 no bounds");
}

#[test]
fn a_field_read_is_a_value_conditions_bound() {
    let body = "  var xs = [1, 2, 3]\n  let a = p.0\n  if a >= 0 && a < 3 { xs[a] } else { 0 }";
    has(
        &checks(&function("(p: (i64, i64)) -> i64", body), "f"),
        "6:24 bounds",
    );
}

#[test]
fn a_closure_is_analysed_as_a_body() {
    let body = "  let xs = [1, 2, 3]\n  let g = |i: i64| xs[i]\n  g(k)";
    has(
        &checks(&function("(k: i64) -> i64", body), "f"),
        "5:20 no bounds",
    );
    // A `return` in a closure ends the closure, not the body that makes it.
    let body = "  let xs = [1, 2, 3]\n  let g = |i: i64| { return i }\n  xs[k] + g(1)";
    has(
        &checks(&function("(k: i64) -> i64", body), "f"),
        "6:3 no bounds",
    );
}
