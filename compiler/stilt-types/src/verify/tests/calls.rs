//! Calls: the lengths that facts.writes-through-calls's table gives a list taken `inout`, the
//! checks of facts.proved-indexes's table, and the calls and places that are linear forms
//! (facts.linear-forms), read through `List.repeat`'s length and through indexes.

use super::{checks, has};

/// A program of one function `f`, whose body starts on line 4.
fn function(signature: &str, body: &str) -> String {
    format!("module main\nuse std.array\nfn f{signature} {{\n{body}\n}}\n")
}

#[test]
fn remove_and_pop_take_one_element_away() {
    // ℓ is 3; `remove` makes it 2 and `pop`, with ℓ ≥ 1 proved, 1.
    let body = "  var xs = [1, 2, 3]\n  let _ = xs.remove(0)\n  let a = xs[1]\n  let b = xs[2]\n  \
                let _ = xs.pop()\n  a + b + xs[0] + xs[1]";
    let found = checks(&function("() -> i64", body), "f");
    has(&found, "5:11 bounds");
    has(&found, "6:11 bounds");
    has(&found, "7:11 no bounds");
    has(&found, "9:11 bounds");
    has(&found, "9:19 no bounds");
}

#[test]
fn a_pop_of_a_list_that_may_be_empty() {
    // Without ℓ ≥ 1, `pop` gives a length of at least 0 and at most ℓ: nothing about `n`, and
    // a length below 3 where `n` is.
    let body = "  var xs = ys\n  let n = xs.len()\n  let _ = xs.pop()\n  let one = [0]\n  \
                let a = if n <= 1 { one[n - 1] } else { 0 }\n  let three = [0, 0, 0]\n  \
                a + if n < 3 { three[xs.len()] } else { 0 }";
    let found = checks(&function("(ys: List<i64>) -> i64", body), "f");
    has(&found, "8:23 no bounds");
    has(&found, "10:18 bounds");
}

#[test]
fn a_clear_leaves_no_element() {
    let body = "  var xs = [1, 2]\n  xs.clear()\n  xs.push(5)\n  let two = [0, 0]\n  two[xs.len()] + xs[0]";
    let found = checks(&function("() -> i64", body), "f");
    has(&found, "8:3 bounds");
    has(&found, "8:19 bounds");
}

#[test]
fn an_insert_into_an_element_reads_no_length() {
    // The receiver's place goes through `xss[0]`, so the table reads no length for it: only
    // the outer list's is known.
    let body = "  var xss = [[1], [2], [3]]\n  xss[0].insert(3, 9)\n  xss[1][0]";
    let found = checks(&function("() -> i64", body), "f");
    has(&found, "5:3 no bounds");
}

#[test]
fn forms_give_a_repeated_lists_length() {
    // `n + 1`, `2 + k` and `k - 1` are linear forms, so each list's length is the form.
    let body = "  if n >= 0 && k >= 2 {\n    let xs = List.repeat(0, n + 1)\n    \
                let ys = List.repeat(0, 2 + k)\n    let zs = List.repeat(0, k - 1)\n    \
                xs[n] + ys[k + 1] + zs[k - 2] + zs[k - 1]\n  } else { 0 }";
    let found = checks(
        &function("<n: i64>(v: array.Array<i64, n>, k: i64) -> i64", body),
        "f",
    );
    has(&found, "8:5 bounds");
    has(&found, "8:13 bounds");
    has(&found, "8:25 bounds");
    has(&found, "8:37 no bounds");
}

#[test]
fn lengths_and_conversions_are_forms() {
    // `xs.len()`, an array's `len()` and `k.to_i64()` are linear forms; `k.abs()` is not.
    let body = "  if k >= 0 && k < 1 && xs.len() > 2 {\n    let ws = List.repeat(0, xs.len())\n    \
                let vs = List.repeat(0, a.len())\n    let us = List.repeat(0, k.to_i64() + 1)\n    \
                let one = [0]\n    vs[2] + vs[3] + us[k.to_i64()] + one[k.abs().to_i64()] + ws[2]\n  \
                } else { 0 }";
    let found = checks(
        &function(
            "(xs: List<i64>, a: array.Array<i64, 3>, k: i32) -> i64",
            body,
        ),
        "f",
    );
    has(&found, "9:5 bounds");
    has(&found, "9:13 no bounds");
    has(&found, "9:21 bounds");
    has(&found, "9:38 no bounds");
    has(&found, "9:62 bounds");
}

#[test]
fn an_arrays_length_through_a_place() {
    // `g.cells` and `rows[i]` are places whose evaluation changes nothing; `rows[k * 2]` has an
    // index of no linear form, so its `len()` has its type's bounds only.
    let text = "module main\nuse std.array\ntype Grid = { cells: array.Array<i64, 4> }\n\n\
                fn f(g: Grid, rows: array.Array<array.Array<i64, 3>, 2>, k: i64) -> i64 {\n  \
                let four = [0, 0, 0, 0]\n  let three = [0, 0, 0]\n  \
                let a = four[g.cells.len() - 1]\n  let b = three[rows[1].len() - 1]\n  \
                a + b + three[rows[k * 2].len() - 1]\n}\n";
    let found = checks(text, "f");
    has(&found, "8:11 bounds");
    has(&found, "9:11 bounds");
    has(&found, "10:11 no bounds");
}

#[test]
fn remove_and_pop_leave_no_more_than_one_fewer() {
    // After either, ℓ is 2, so `three[xs.len()]` is in range.
    let body = "  let three = [0, 0, 0]\n  var xs = [1, 2, 3]\n  let _ = xs.remove(0)\n  \
                let a = three[xs.len()]\n  xs.push(4)\n  let _ = xs.pop()\n  a + three[xs.len()]";
    let found = checks(&function("() -> i64", body), "f");
    has(&found, "7:11 bounds");
    has(&found, "10:7 bounds");
}

#[test]
fn swap_needs_both_indexes_in_range() {
    // facts.proved-indexes: `0 ≤ i < ℓ` and `0 ≤ j < ℓ`.
    let body = "  var xs = [1, 2, 3]\n  xs.swap(0, 2)\n  xs.swap(0, 3)\n  xs.swap(3, 0)\n  xs[0]";
    let found = checks(&function("() -> i64", body), "f");
    has(&found, "5:3 bounds");
    has(&found, "6:3 no bounds");
    has(&found, "7:3 no bounds");
}

#[test]
fn slice_needs_its_ends_ordered_within_the_length() {
    // facts.proved-indexes: `0 ≤ a ≤ b ≤ ℓ`, the receiver's length read where it is evaluated.
    let body = "  let xs = [1, 2, 3]\n  if k >= 0 && k <= 1 {\n    let a = xs.slice(1, 3)\n    \
                let b = xs.slice(k + 1, k + 2)\n    let c = xs.slice(k + 2, k + 1)\n    \
                let d = xs.slice(0, 4)\n    let e = xs.slice(2, 1)\n    \
                a.len() + b.len() + c.len() + d.len() + e.len()\n  } else { 0 }";
    let found = checks(&function("(k: i64) -> i64", body), "f");
    has(&found, "6:13 bounds");
    has(&found, "7:13 bounds");
    has(&found, "8:13 no bounds");
    has(&found, "9:13 no bounds");
    has(&found, "10:13 no bounds");
}

#[test]
fn an_argument_keeps_its_value_while_the_next_ones_run() {
    // values.left-to-right: `k % 3` is read before the block runs, and its term, which no
    // binding holds, lasts until the call starts, past the block's statement.
    let body = "  var xs = [1, 2, 3]\n  if k >= 0 {\n    xs.insert(k % 3, {\n      let t = 0\n      t\n    })\n  }\n  0";
    let found = checks(&function("(k: i64) -> i64", body), "f");
    has(&found, "6:5 bounds");
}

/// A program in which `f`'s `with` around `call` ends, through the handler of `Stop`, which
/// takes control, before `xs` gets back its three elements (facts.paths-that-leave).
fn ended(signature: &str, items: &str, call: &str) -> String {
    format!(
        "module main\neffect Stop {{\n  fn stop()\n}}\n{items}\nfn f{signature} {{\n  var xs = [1, 2, 3]\n  \
         let stop = handler Stop -> () {{ fn stop() {{}} }}\n  with stop {{\n    xs.clear()\n    \
         {call}\n    xs.push(1)\n    xs.push(2)\n    xs.push(3)\n  }}\n  xs[2]\n}}\n"
    )
}

#[test]
fn a_call_whose_row_holds_an_effect_may_end_a_with() {
    let text = ended(
        "() -> i64",
        "fn stops() / Stop { Stop.stop() }\n",
        "stops()",
    );
    has(&checks(&text, "f"), "17:3 no bounds");
    // A call of a function that performs nothing doesn't.
    let text = ended("() -> i64", "fn calm() {}\n", "calm()");
    has(&checks(&text, "f"), "17:3 bounds");
}

#[test]
fn a_call_through_a_function_value_may_end_a_with() {
    // `g`'s row pairs `Stop` with the caller's `e` (handlers.with-pairing), so its performance
    // of `Stop` may end the `with`; an escaping `g` with no row performs nothing.
    let text = ended("<e>(escaping g: fn() / {Stop, e}) -> i64 / e", "", "g()");
    has(&checks(&text, "f"), "16:3 no bounds");
    let text = ended("(escaping g: fn()) -> i64", "", "g()");
    has(&checks(&text, "f"), "16:3 bounds");
}

#[test]
fn a_place_through_a_key_keeps_the_keys_present() {
    // facts.map-keys: `bump(inout n[k])` gives `n` a new version with its keys present, and
    // `touch(inout n)` one with none.
    let text = |call: &str| {
        format!(
            "module main\nfn bump(inout x: i64) {{ x += 1 }}\nfn touch(inout m: Map<str, i64>) {{}}\n\
             fn f(m: Map<str, i64>, k: str) -> i64 {{\n  var n = m\n  n[k] = 1\n  n[\"z\"] = 2\n  {call}\n  n[\"z\"]\n}}\n"
        )
    };
    has(&checks(&text("bump(inout n[k])"), "f"), "9:3 missing-key");
    has(&checks(&text("touch(inout n)"), "f"), "9:3 no missing-key");
}

#[test]
fn a_conversion_is_a_form_and_abs_is_not() {
    // `List.repeat`'s length is a form for `k.to_i64() + 1`, and `k.abs()` has none.
    let body = "  if k >= 0 && k <= 0 {\n    let a = List.repeat(0, k.to_i64() + 1)\n    \
                let b = List.repeat(0, k.abs().to_i64() + 1)\n    a[0] + b[0]\n  } else { 0 }";
    let found = checks(&function("(k: i32) -> i64", body), "f");
    has(&found, "7:5 bounds");
    has(&found, "7:12 no bounds");
}
