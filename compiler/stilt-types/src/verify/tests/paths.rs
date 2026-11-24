//! Paths that meet and paths that leave (facts.paths-that-leave): handlers that end a `with`, names
//! of a `when`, and loops whose widening keeps a threshold's bound.

use super::{checks, has, unproved};

/// The notes of E0204 in a module limited by `without panic` holding `code`.
fn notes(code: &str) -> Vec<String> {
    unproved(&format!("module main\nwithout panic\n\n{code}"))
}

#[test]
fn a_handler_that_takes_control_ends_the_with() {
    // The `push` may not run: `stop` ends the `with` before it, directly or through `ask`.
    let code = "effect Stop {\n  fn stop()\n}\n\neffect Ask {\n  fn ask() -> i64 / Stop\n}\n\n\
                fn direct() -> i64 {\n  var xs: List<i64> = []\n  let stop = handler Stop -> () { fn stop() {} }\n  \
                with stop {\n    Stop.stop()\n    xs.push(1)\n  }\n  xs[0]\n}\n\n\
                fn through() -> i64 {\n  var xs: List<i64> = []\n  let stop = handler Stop -> () { fn stop() {} }\n  \
                let ask = handler Ask {\n    fn ask() -> i64 {\n      Stop.stop()\n      1\n    }\n  }\n  \
                with stop {\n    with ask {\n      let _ = Ask.ask()\n      xs.push(1)\n    }\n  }\n  xs[0]\n}\n";
    let text = format!("module main\nwithout panic\n\n{code}");
    let found = unproved(&text);
    assert_eq!(found, ["19:3 no bounds", "37:3 no bounds"]);
}

#[test]
fn a_handler_that_resumes_ends_nothing() {
    let code = "effect Ask {\n  fn ask() -> i64\n}\n\n\
                fn f() -> i64 {\n  var xs: List<i64> = []\n  let ask = handler Ask { fn ask() -> i64 { 1 } }\n  \
                with ask {\n    let _ = Ask.ask()\n    xs.push(1)\n  }\n  xs[0]\n}\n";
    assert_eq!(notes(code), Vec::<String>::new());
}

#[test]
fn the_names_of_a_when_have_no_terms() {
    let code = "use std.sync\n\ntype Box = { n: i64 }\n\n\
                fn f(a: sync.Shared<Box>, xs: List<i64>) -> i64 {\n  when a {\n    a.n = 0\n    \
                if a.n >= 0 && a.n < xs.len() { xs[a.n] } else { 0 }\n  }\n}\n";
    let found = notes(code);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(found[0].ends_with("no bounds"), "{found:?}");
}

#[test]
fn widening_keeps_a_thresholds_bound() {
    // The bound 10 is a literal of the loop, so the head keeps `i <= 10` past the visits that
    // climb to it, and the index into eleven elements is proved.
    let code = "fn f() -> i64 {\n  let xs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]\n  var i = 0\n  var s = 0\n  \
                while i < 10 {\n    if i < 10 { i += 1 }\n    s += xs[i]\n  }\n  s\n}\n";
    let text = format!("module main\nwithout panic\n\n{code}");
    has(&checks(&text, "f"), "10:10 bounds");
}

#[test]
fn a_fact_one_branch_loses_doesnt_hold_after() {
    let code = "fn f(xs: List<i64>, c: bool) -> i64 {\n  var ys = xs\n  if c { ys.push(1) } else { ys.clear() }\n  ys[0]\n}\n";
    assert_eq!(notes(code), ["7:3 no bounds"]);
    let code = "fn f(xs: List<i64>, c: bool) -> i64 {\n  var ys = xs\n  if c { ys.push(1) } else { ys.push(2) }\n  ys[0]\n}\n";
    assert_eq!(notes(code), Vec::<String>::new());
}
