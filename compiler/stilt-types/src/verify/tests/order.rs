//! The order of evaluation (facts.analysis-order): each operation is checked with the values it
//! uses, as they were evaluated, and the facts where it happens.

use super::unproved;

/// The notes of E0204 in a module limited by `without panic` holding `code`.
fn notes(code: &str) -> Vec<String> {
    unproved(&format!("module main\nwithout panic\n\n{code}"))
}

#[test]
fn a_store_checks_the_index_evaluated_before_its_value() {
    let code = "fn f(n: i64) -> List<i64> {\n  var ys = [0, 0, 0, 0, 0, 0]\n  var j = n\n  \
                if j >= 6 { ys[j] = { j = 5; 1 } }\n  ys\n}\n";
    assert_eq!(notes(code), ["7:15 no bounds"]);
    // The index's old value, in range, is the one the store checks.
    let code = "fn f(n: i64) -> List<i64> {\n  var ys = [0, 0, 0, 0, 0, 0]\n  var j = n\n  \
                if j >= 0 && j < 6 { ys[j] = { j = 9; 1 } }\n  ys\n}\n";
    assert_eq!(notes(code), Vec::<String>::new());
}

#[test]
fn a_store_checks_the_length_after_its_value() {
    let code = "fn f() -> List<i64> {\n  var xs = [1, 2]\n  xs[0] = { xs.clear(); 1 }\n  xs\n}\n";
    assert_eq!(notes(code), ["6:3 no bounds"]);
}

#[test]
fn a_read_checks_the_length_before_its_index() {
    let code = "fn f() -> i64 {\n  var xs = [1, 2, 3]\n  xs[{ xs.push(0); 3 }]\n}\n";
    assert_eq!(notes(code), ["6:3 no bounds"]);
    // values.index-reads: the list is read before the index clears it.
    let code = "fn f() -> i64 {\n  var xs = [1]\n  xs[{ xs.clear(); 0 }]\n}\n";
    assert_eq!(notes(code), Vec::<String>::new());
}

#[test]
fn a_key_is_checked_after_the_value_that_clears_its_map() {
    let code = "type Count = { n: i64 }\n\nfn bump(inout c: Count, by: i64) { c.n += by }\n\n\
                fn f() -> Map<str, Count> {\n  var m: Map<str, Count> = Map.new()\n  m[\"a\"] = Count { n: 1 }\n  \
                m[\"a\"].n = { m.clear(); 0 }\n  bump(inout m[\"a\"], { m.clear(); 1 })\n  m\n}\n";
    assert_eq!(notes(code), ["11:3 no missing-key", "12:14 no missing-key"]);
}

#[test]
fn calls_read_their_arguments_in_turn() {
    let code = "fn f(n: i64) -> List<i64> {\n  var xs = [1, 2, 3]\n  var i = n\n  \
                if i >= 3 { xs.swap(i, { i = 0; 0 }) }\n  xs.insert(3, { xs.clear(); 9 })\n  xs\n}\n";
    assert_eq!(notes(code), ["7:15 no bounds", "8:3 no bounds"]);
}

#[test]
fn an_operand_is_read_before_the_next_one_runs() {
    let code = "fn f(xs: List<i64>, n: i64) -> i64 {\n  var i = n\n  if i >= 0 && i < xs.len() {\n    \
                i = i + { i = 0; 1 }\n    xs[i]\n  } else { 0 }\n}\n";
    assert_eq!(notes(code), ["8:5 no bounds"]);
}

#[test]
fn a_size_read_through_a_block_has_no_linear_form() {
    let code = "use std.array\n\nfn f(a: array.Array<i64, 3>, n: i64) -> i64 {\n  var i = n\n  \
                if i >= 0 && i < ({ i = 100; a }).len() { a[i] } else { 0 }\n}\n";
    let found = notes(code);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(found[0].ends_with("no bounds") || found[0].ends_with("no bounds"));
}

#[test]
fn a_match_whose_scrutinee_or_guard_changes_the_list() {
    let code = "fn grow_by(inout n: i64) -> bool {\n  n += 5\n  true\n}\n\n\
                fn f() -> i64 {\n  var xs = [1, 2, 3]\n  let got = match xs.pop() { Some(x) => x, None => 0 }\n  \
                got + xs[2]\n}\n\n\
                fn g() -> i64 {\n  let xs = [1, 2, 3]\n  var k = 0\n  let got = match k {\n    \
                _ if grow_by(inout k) => 1\n    _ => 2\n  }\n  got + xs[k]\n}\n";
    assert_eq!(notes(code), ["12:9 no bounds", "22:9 no bounds"]);
}

#[test]
fn an_or_patterns_guard_runs_once_for_each_way() {
    let code = "fn pops(inout xs: List<i64>) -> bool {\n  let _ = xs.pop()\n  false\n}\n\n\
                fn f(k: i64) -> i64 {\n  var xs = [1, 2, 3]\n  match k {\n    \
                0 | 1 if pops(inout xs) => 0\n    _ => xs[1]\n  }\n}\n";
    let found = notes(code);
    assert_eq!(found, ["13:10 no bounds"]);
}

#[test]
fn the_right_operand_of_and_may_change_the_list() {
    let code = "fn pops(inout xs: List<i64>) -> bool {\n  let _ = xs.pop()\n  true\n}\n\n\
                fn f() -> i64 {\n  var xs = [1, 2, 3]\n  if xs.len() > 2 && pops(inout xs) { xs[2] } else { 0 }\n}\n";
    assert_eq!(notes(code), ["11:39 no bounds"]);
}

#[test]
fn a_caught_raise_keeps_what_the_call_wrote() {
    let code = "type Oops = { code: i64 }\n\nfn drain(inout xs: List<i64>) -> i64 / raise<Oops> {\n  \
                xs.clear()\n  raise Oops { code: 1 }\n}\n\n\
                fn f() -> i64 {\n  var xs = [1, 2, 3]\n  try drain(inout xs) catch Oops { code } => code + xs[0]\n}\n";
    assert_eq!(notes(code), ["13:53 no bounds"]);
}

#[test]
fn a_projection_lends_its_place() {
    let code = "fn whole(inout xs: List<i64>) -> inout List<i64> {\n  xs.push(0)\n  yield xs\n  xs[0] = 1\n}\n";
    assert_eq!(notes(code), ["7:3 no bounds"]);
}

#[test]
fn a_guard_runs_again_for_each_way_of_a_nested_or_pattern() {
    // patterns.guards: a value that both ways of `0 | _` match runs the guard twice, so `xs` may
    // have lost two elements, wherever the or-pattern sits; a guard without one runs once.
    let shapes = [
        ("k", "0 | _"),
        ("(k, k)", "(0 | _, _)"),
        ("Some(k)", "Some(0 | _)"),
        ("[k]", "[0 | _]"),
        ("(P { n: k })", "P { n: 0 | _ }"),
    ];
    for (scrutinee, pattern) in shapes {
        let code = format!(
            "type P = {{ n: i64 }}\n\nfn f(k: i64) -> i64 {{\n  var xs = [1, 2, 3]\n  match {scrutinee} {{\n    \
             {pattern} if {{ let _ = xs.pop(); false }} => 0\n    _ => xs[1]\n  }}\n}}\n"
        );
        assert_eq!(notes(&code), ["10:10 no bounds"], "{pattern}");
    }
    let code = "fn f(k: i64) -> i64 {\n  var xs = [1, 2, 3]\n  match k {\n    \
                n if { let _ = xs.pop(); n > 0 } => 0\n    _ => xs[1]\n  }\n}\n";
    assert_eq!(notes(code), Vec::<String>::new());
}

#[test]
fn a_literal_arm_fixes_the_scrutinees_form() {
    // facts.match-arms: matching `k + 1` against 3 gives `k = 2`, against `1 | 2` the join of
    // `k = 0` and `k = 1`, and against 0 `k = −1`.
    let code = "fn f(k: i64) -> i64 {\n  let three = [0, 0, 0]\n  match k + 1 {\n    \
                3 => three[k]\n    1 | 2 => three[k]\n    0 => three[k]\n    _ => 0\n  }\n}\n";
    assert_eq!(notes(code), ["9:10 no bounds"]);
}
