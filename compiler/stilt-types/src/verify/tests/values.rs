//! Indexes, divisions and map keys (facts.proved-indexes, facts.proved-divisions and
//! facts.map-keys).

use super::{checks, has, unproved};

/// A program of one function `f`, limited by `without panic`, with `body` after its signature.
fn limited(signature: &str, body: &str) -> String {
    format!("module main\nwithout panic\n\nfn f{signature} {{\n{body}\n}}\n")
}

#[test]
fn a_counter_over_the_length_indexes_in_range() {
    let text = limited(
        "(xs: List<i64>) -> i64",
        "  var s = 0\n  for i in 0..xs.len() { s += xs[i] }\n  s",
    );
    has(&checks(&text, "f"), "6:31 bounds");
    let text = limited(
        "(xs: List<i64>) -> i64",
        "  var s = 0\n  for i in 0..xs.len() - 1 { s += xs[i + 1] }\n  s",
    );
    has(&checks(&text, "f"), "6:35 bounds");
    // One past the end: the upper fact is the one it can't prove.
    let text = limited(
        "(xs: List<i64>) -> i64",
        "  var s = 0\n  for i in 0..xs.len() { s += xs[i + 1] }\n  s",
    );
    assert_eq!(unproved(&text), ["6:31 no bounds"]);
}

#[test]
fn guards_bound_an_index() {
    let text = limited(
        "(xs: List<i64>, i: i64) -> i64",
        "  if i >= 0 && i < xs.len() { xs[i] } else { 0 }",
    );
    has(&checks(&text, "f"), "5:31 bounds");
    let text = limited(
        "(xs: List<i64>, i: i64) -> i64",
        "  if i >= 0 && i <= xs.len() { xs[i] } else { 0 }",
    );
    assert_eq!(unproved(&text), ["5:32 no bounds"]);
    let text = limited(
        "(xs: List<i64>) -> i64",
        "  if !xs.is_empty() { xs[0] } else { 0 }",
    );
    has(&checks(&text, "f"), "5:23 bounds");
    let text = limited(
        "(xs: List<i64>) -> i64",
        "  if !xs.is_empty() { xs[1] } else { 0 }",
    );
    assert_eq!(unproved(&text), ["5:23 no bounds"]);
}

#[test]
fn a_parameter_is_never_an_index_in_range() {
    let text = limited("(xs: List<i64>, i: i64) -> i64", "  xs[i]");
    assert_eq!(unproved(&text), ["5:3 no bounds"]);
}

#[test]
fn literals_and_pushes_make_lengths() {
    let text = limited("() -> i64", "  let xs = [1, 2, 3]\n  xs[2]");
    has(&checks(&text, "f"), "6:3 bounds");
    let text = limited("() -> i64", "  let xs = [1, 2, 3]\n  xs[3]");
    assert_eq!(unproved(&text), ["6:3 no bounds"]);
    let text = limited(
        "() -> List<i64>",
        "  var xs = []\n  xs.push(1)\n  xs.push(2)\n  xs[1] = 5\n  xs",
    );
    has(&checks(&text, "f"), "8:3 bounds");
    let text = limited(
        "() -> List<i64>",
        "  var xs = []\n  xs.push(1)\n  xs[1] = 5\n  xs",
    );
    assert_eq!(unproved(&text), ["7:3 no bounds"]);
}

#[test]
fn an_array_is_indexed_below_its_size() {
    let text = "module main\nwithout panic\nuse std.array\n\ntype Grid = { cells: array.Array<i64, 4> }\n\n\
                fn f(a: array.Array<i64, 4>, g: Grid) -> i64 { a[3] + g.cells[3] }\n";
    let found = checks(text, "f");
    has(&found, "7:48 bounds");
    has(&found, "7:55 bounds");
    let text = "module main\nwithout panic\nuse std.array\n\nfn f(a: array.Array<i64, 4>) -> i64 { a[4] }\n";
    assert_eq!(unproved(text), ["5:39 no bounds"]);
}

#[test]
fn a_byte_converted_indexes_a_table_of_256() {
    let text = "module main\nwithout panic\nuse std.array\n\nfn f(t: array.Array<i64, 256>, b: u8) -> i64 { t[b.to_i64()] }\n";
    has(&checks(text, "f"), "5:48 bounds");
    let text = "module main\nwithout panic\nuse std.array\n\nfn f(t: array.Array<i64, 255>, b: u8) -> i64 { t[b.to_i64()] }\n";
    assert_eq!(unproved(text), ["5:48 no bounds"]);
}

#[test]
fn a_remainder_by_the_length_is_in_range() {
    let text = limited(
        "(xs: List<i64>, h: i64) -> i64",
        "  if h >= 0 && !xs.is_empty() { xs[h % xs.len()] } else { 0 }",
    );
    has(&checks(&text, "f"), "5:33 bounds");
}

#[test]
fn rows_products_and_pops_stay_checked() {
    let text = limited(
        "(rows: List<List<i64>>) -> i64",
        "  if !rows.is_empty() { rows[0][0] } else { 0 }",
    );
    assert_eq!(unproved(&text), ["5:25 no bounds"]);
    let text = limited(
        "(cells: List<i64>, x: i64, y: i64, n: i64) -> i64",
        "  cells[y * n + x]",
    );
    assert_eq!(unproved(&text), ["5:3 no bounds"]);
    let text = limited(
        "(xs: List<i64>) -> i64",
        "  var ys = xs\n  let _ = ys.pop()\n  ys[0]",
    );
    assert_eq!(unproved(&text), ["7:3 no bounds"]);
}

#[test]
fn the_table_of_calls_checks_their_arguments() {
    let body = "  var ys = [1, 2, 3]\n  ys.insert(3, 4)\n  ys.swap(0, 3)\n  let _ = ys.remove(0)\n  ys.slice(1, 3)";
    let found = checks(&limited("() -> List<i64>", body), "f");
    has(&found, "6:3 bounds");
    has(&found, "7:3 bounds");
    has(&found, "8:11 bounds");
    has(&found, "9:3 bounds");
    let body = "  var ys = [1, 2, 3]\n  ys.insert(4, 4)\n  ys.slice(2, 1)";
    assert_eq!(
        unproved(&limited("() -> List<i64>", body)),
        ["6:3 no bounds", "7:3 no bounds"]
    );
}

#[test]
fn divisions_by_a_proved_divisor() {
    let found = checks(
        &limited(
            "(n: i64, d: i64) -> i64",
            "  if d != 0 { n / d } else { 0 }",
        ),
        "f",
    );
    has(&found, "5:15 divide-by-zero");
    let found = checks(
        &limited(
            "(n: i64, d: i64) -> i64",
            "  if d == 0 { return 0 }\n  n / d",
        ),
        "f",
    );
    has(&found, "6:3 divide-by-zero");
    let found = checks(
        &limited(
            "(n: i64, d: i64) -> i64",
            "  match d { 0 => 0, _ => n / d }",
        ),
        "f",
    );
    has(&found, "5:26 divide-by-zero");
    let found = checks(
        &limited(
            "(n: i64) -> i64",
            "  var s = 0\n  for d in 1..10 { s += n / d }\n  s",
        ),
        "f",
    );
    has(&found, "6:25 divide-by-zero");
}

#[test]
fn divisions_that_stay_checked() {
    let text = limited("(n: i64, d: i64) -> i64", "  n / d");
    assert_eq!(unproved(&text), ["5:3 no divide-by-zero"]);
    let text = limited(
        "(n: i64, d: i64) -> i64",
        "  var e = d\n  if e != 0 { e -= 1\n    n / e } else { 0 }",
    );
    assert_eq!(unproved(&text), ["7:5 no divide-by-zero"]);
    let text = limited(
        "(n: i64, x: i64) -> i64",
        "  let d = x\n  if x - 1 != 0 { n / d } else { 0 }",
    );
    assert_eq!(unproved(&text), ["6:19 no divide-by-zero"]);
}

#[test]
fn stored_and_contained_keys_are_found() {
    for key in ["str", "i64"] {
        let sig = format!("(m: Map<{key}, i64>, k: {key}) -> i64");
        let found = checks(&limited(&sig, "  var n = m\n  n[k] = 1\n  n[k]"), "f");
        has(&found, "7:3 missing-key");
        let found = checks(&limited(&sig, "  var n = m\n  n.insert(k, 1)\n  n[k]"), "f");
        has(&found, "7:3 missing-key");
        let found = checks(
            &limited(&sig, "  if m.contains(k) { m[k] } else { 0 }"),
            "f",
        );
        has(&found, "5:22 missing-key");
    }
}

#[test]
fn keys_that_are_lost() {
    let sig = "(m: Map<str, i64>, k: str, j: str) -> i64";
    let lost = [
        (
            "  var n = m\n  n[k] = 1\n  let _ = n.remove(j)\n  n[k]",
            "8:3",
        ),
        (
            "  var n = m\n  var q = k\n  n[q] = 1\n  q = j\n  n[q]",
            "9:3",
        ),
        (
            "  var n = m\n  var q = k\n  n[q] = { q = \"b\"; 1 }\n  n[q]",
            "8:3",
        ),
        (
            "  var n = m\n  var q = k\n  n.insert(q, { q = \"b\"; 1 })\n  n[q]",
            "8:3",
        ),
        ("  var n = m\n  n[k] = 1\n  n.clear()\n  n[k]", "8:3"),
        ("  var n = m\n  n[\"{k}\"] = 1\n  n[\"{k}\"]", "7:3"),
        (
            "  var n = m\n  n[k] = 1\n  n[k] += { n.clear(); 1 }\n  n[k]",
            "7:3",
        ),
    ];
    for (body, at) in lost {
        let found = unproved(&limited(sig, body));
        assert!(
            found.iter().any(|f| f == &format!("{at} no missing-key")),
            "{body}: {found:?}"
        );
    }
}

#[test]
fn a_key_with_an_eq_of_its_own_is_never_found_again() {
    let text = "module main\nwithout panic\n\ntype K = { n: i64 }\n\nimpl Eq for K {\n  fn eq(self, o: K) -> bool { self.n == o.n }\n}\n\
                impl Hash for K {\n  fn hash(self) -> u64 { self.n.hash() }\n}\n\n\
                fn f(m: Map<K, i64>, k: K) -> i64 {\n  var n = m\n  n[k] = 1\n  n[k]\n}\n";
    let found = unproved(text);
    assert!(
        found.iter().any(|f| f.starts_with("16:3 no missing-key")),
        "{found:?}"
    );
}

#[test]
fn facts_that_both_branches_keep() {
    let body = "  var n = m\n  if c { n[\"x\"] = 1 } else { n[\"x\"] = 2 }\n  n[\"x\"]";
    let found = checks(&limited("(m: Map<str, i64>, c: bool) -> i64", body), "f");
    has(&found, "7:3 missing-key");
    let body =
        "  var d = 1\n  if a != 0 {\n    if c { d = a } else { d = a }\n    n / d\n  } else { 0 }";
    let found = checks(&limited("(n: i64, a: i64, c: bool) -> i64", body), "f");
    has(&found, "8:5 divide-by-zero");
    // One branch loses the key.
    let body = "  var n = m\n  if c { n[\"x\"] = 1 }\n  n[\"x\"]";
    assert_eq!(
        unproved(&limited("(m: Map<str, i64>, c: bool) -> i64", body)),
        ["7:3 no missing-key"]
    );
}
