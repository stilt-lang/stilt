//! Tests of the rules of acceptance (facts.rules-of-acceptance): what each proves of small
//! bodies, and what E0204 says the closest rule needs of what none proves, each case taken from
//! the record's required tests, with the verdicts the rules give by reasoning. The reference interpreter's own
//! tests (`interpreter/test/test_accept.ml`) hold the same programs and the same messages.

use stilt_diag::LineIndex;

use crate::facts::proved_checks;
use crate::verify::tests::{Database, body_of, program};

/// Each error of the program of one file made of `lines`, as `LINE: NEED` for an E0204, with
/// what its help says the closest rule needs, and as `LINE: CODE MESSAGE` for another.
fn needs(lines: &[&str]) -> Vec<String> {
    let text = lines.join("\n");
    let db = Database::default();
    let (program, _) = program(&db, &text);
    let index = LineIndex::new(&text);
    crate::check(&db, program)
        .iter()
        .filter(|d| d.diagnostic.is_error())
        .map(|d| {
            let line = index.position(&text, d.diagnostic.range.start()).line;
            let message = &d.diagnostic.message;
            match d.diagnostic.help() {
                need if d.diagnostic.code.as_str() == "E0204" => {
                    let need = need.trim_end_matches('.');
                    let mut chars = need.chars();
                    let first = chars.next().map(|c| c.to_lowercase().collect::<String>());
                    format!("{line}: {}{}", first.unwrap_or_default(), chars.as_str())
                }
                _ => format!("{line}: {} {message}", d.diagnostic.code.as_str()),
            }
        })
        .collect()
}

/// The checks of the function `name` that a rule proves, as `LINE CHECK by a RULE`.
fn proved(lines: &[&str], name: &str) -> Vec<String> {
    let text = lines.join("\n");
    let db = Database::default();
    let (program, file) = program(&db, &text);
    let index = LineIndex::new(&text);
    let body = body_of(&db, program, file, name);
    proved_checks(&db, program, file, body)
        .iter()
        .map(|p| {
            let line = index.position(&text, p.at.start()).line;
            let check = p.check.shown().unwrap_or_default();
            format!("{line} {check} by a {}", p.rule.name())
        })
        .collect()
}

/// facts.range-loops: indexes that range loops prove.
#[test]
fn range_loops_accept() {
    let lines = [
        "fn total(xs: List<i64>) -> i64 without panic {",
        "var s = 0",
        "for i in 0..xs.len() { s += xs[i] }",
        "for i in 0..xs.len() - 1 { s += xs[i] + xs[i + 1] }",
        "for i in 1..xs.len() { s += xs[i - 1] }",
        "var ys = xs",
        "for i in 0..ys.len() { ys[i] = s }",
        "s + ys[0] * 0",
        "}",
    ];
    let expected = ["8: a guard needs a test that gives `0 < ys.len()`"];
    assert_eq!(needs(&lines), expected);
    let shown = [
        "3 bounds by a range loop",
        "4 bounds by a range loop",
        "4 bounds by a range loop",
        "5 bounds by a range loop",
        "7 bounds by a range loop",
    ];
    assert_eq!(proved(&lines, "total"), shown);
}

/// facts.closest-rule: what the range loop needs, in the order facts.range-loops lists it.
#[test]
fn range_loops_need() {
    let lines = [
        "fn upto(xs: List<i64>, n: i64) -> i64 without panic {",
        "var s = 0",
        "for i in 0..n { s += xs[i] }",
        "for i in n..xs.len() { s += xs[i] }",
        "for i in 0..xs.len() - 1 { s += xs[i + 2] }",
        "for i in 1..xs.len() { s += xs[i - 2] }",
        "for i in 0..=xs.len() { s += xs[i] + xs[2 * i] }",
        "for i in 0..xs.len() { let at = || xs[i]",
        "s += at() }",
        "s",
        "}",
        "fn pushed(xs: List<i64>) -> List<i64> without panic {",
        "var ys = xs",
        "for i in 0..ys.len() {",
        "ys[i] = 1",
        "ys.push(0)",
        "}",
        "ys",
        "}",
    ];
    let expected = [
        "3: a range loop needs it to end at `xs.len()`, not at `n`",
        "4: a range loop needs it to start at a value known non-negative",
        "5: a range loop needs it to end at `xs.len() - 2`, not at `xs.len() - 1`",
        "6: a range loop needs it to start at `2` or above",
        // One error for the line, whose help says what each of its accesses needs
        // (facts.without).
        "7: a range loop needs it to end at `xs.len()`, not at `..=xs.len()`. A range loop \
         needs the index to be `i`, `i + k` or `i - k`",
        "8: a range loop needs the index outside closures",
        "15: a range loop needs a body that keeps the length of `ys`, which line 16 changes",
    ];
    assert_eq!(needs(&lines), expected);
}

/// facts.guards: indexes that guards prove, the sieve's among them.
#[test]
fn guards_accept() {
    let lines = [
        "fn at(xs: List<i64>, i: i64) -> i64 without panic {",
        "if i >= 0 && i < xs.len() { return xs[i] }",
        "if 0 <= i { if xs.len() > i { return xs[i] } }",
        "if !xs.is_empty() { return xs[0] }",
        "if i < 0 || i >= xs.len() { return 0 }",
        "xs[i]",
        "}",
        "fn sieve(m: i64) -> List<bool> without panic, div {",
        "var flags = []",
        "for _ in 0..m + 1 { flags.push(true) }",
        "for i in 2..flags.len() {",
        "var k = i + i",
        "while k < flags.len() {",
        "flags[k] = false",
        "k += i",
        "}",
        "}",
        "flags",
        "}",
    ];
    assert_eq!(needs(&lines), Vec::<String>::new());
    let shown = [
        "2 bounds by a guard",
        "3 bounds by a guard",
        "4 bounds by a guard",
        "6 bounds by a guard",
    ];
    assert_eq!(proved(&lines, "at"), shown);
}

/// facts.closest-rule: what the guard needs, in the order facts.guards lists it.
#[test]
fn guards_need() {
    let lines = [
        "fn at(xs: List<i64>, ys: List<i64>, i: i64, n: i64) -> i64 without panic {",
        "var zs = xs",
        "var j = i",
        "if j >= 0 && j < zs.len() { zs[j] = { j = 5; 1 } }",
        "if i >= 0 && i < zs.len() {",
        "let _ = zs.pop()",
        "return zs[i]",
        "}",
        "if i < xs.len() { return xs[i] }",
        "if i >= 0 && i < ys.len() { return xs[i] }",
        "if i >= 0 && i + 1 < xs.len() { return xs[i + 1] }",
        "if xs[i] > 0 && i >= 0 && i < xs.len() { return 1 }",
        "xs[n * i]",
        "}",
    ];
    let expected = [
        "4: a guard needs nothing between the test and the index to write `j`, which line 4 does",
        "7: a guard needs nothing between the test and the index to change the length of `zs`, which line 6 does",
        "9: a guard needs a test that gives `i >= 0`",
        "10: a guard needs a test that gives `i < xs.len()`",
        "11: a guard needs the index to be a name or a literal",
        "12: a guard needs a test that gives `i >= 0`",
        "13: a guard needs the index to be a name or a literal",
    ];
    assert_eq!(needs(&lines), expected);
}

/// facts.divisors and facts.closest-rule: divisions that divisors prove, and what the divisor needs
/// of the others.
#[test]
fn divisors() {
    let lines = [
        "const TEN: i64 = 10",
        "fn ratio(n: i64, d: i64, e: i64) -> i64 without panic {",
        "var s = n / 2 + n % TEN",
        "if d != 0 { s += n / d }",
        "if 0 > d { s += n / d }",
        "if d == 0 { return s }",
        "for k in 1..10 { s += n / k }",
        "s += n / d",
        "var f = e",
        "if f != 0 {",
        "f -= 1",
        "s += n / f",
        "}",
        "if e - 1 != 0 { s += n / (e - 1) }",
        "s + n / e",
        "}",
    ];
    let expected = [
        "12: a divisor needs nothing between the test and the division to write `f`, which line 11 does",
        "14: a divisor needs to be a name or a literal other than 0",
        "15: a divisor needs a test that gives `e != 0`",
    ];
    assert_eq!(needs(&lines), expected);
    let shown = [
        "3 divide-by-zero by a divisor",
        "4 divide-by-zero by a divisor",
        "5 divide-by-zero by a divisor",
        "7 divide-by-zero by a divisor",
        "8 divide-by-zero by a divisor",
    ];
    assert_eq!(proved(&lines, "ratio"), shown);
}

/// facts.keys and facts.closest-rule: reads of keys that keys prove, and what the key needs of the
/// others.
#[test]
fn keys() {
    let lines = [
        "fn touch(inout m: Map<str, i64>) without panic { m[\"z\"] = 0 }",
        "fn name() -> str { \"a\" }",
        "fn counts(words: List<str>, j: str, k0: str) -> i64 without panic {",
        "var m: Map<str, i64> = Map.new()",
        "for w in words {",
        "if !m.contains(w) { m[w] = 0 }",
        "m[w] += 1",
        "}",
        "var k = k0",
        "m.insert(k, 1)",
        "m[j] = 2",
        "var s = m[k] + m[\"z\"]",
        "k = \"b\"",
        "s += m[k]",
        "m[k] = 1",
        "let _ = m.remove(j)",
        "s += m[k]",
        "m[name()] = 1",
        "s += m[name()] + m[\"{k}\"]",
        "m[\"a\"] = 1",
        "touch(inout m)",
        "s + m[\"a\"]",
        "}",
    ];
    let expected = [
        "12: a key needs a test that gives `m.contains(\"z\")`, or a store of `\"z\"` before it",
        "14: a key needs nothing between to write `k`, which line 13 does",
        "17: a key needs nothing between to change `m` but by storing into it, which line 16 does",
        "19: a key needs to be a name or a literal that doesn't interpolate",
        "22: a key needs nothing between to change `m` but by storing into it, which line 21 does",
    ];
    assert_eq!(needs(&lines), expected);
    let shown = ["7 missing-key by a key", "12 missing-key by a key"];
    assert_eq!(proved(&lines, "counts"), shown);
}

/// facts.keys: a key's type has an `Eq` and a `Hash` structural throughout its parts, so a
/// record with impls of its own isn't one, while the same record without them is.
#[test]
fn keys_of_records() {
    let lines = [
        "type Own = { n: i64 }",
        "impl Eq for Own { fn eq(self, o: Own) -> bool { self.n == o.n } }",
        "impl Hash for Own { fn hash(self) -> u64 { self.n.hash() } }",
        "type Plain = { n: i64 }",
        "fn own(m: Map<Own, i64>, k: Own) -> i64 without panic {",
        "if m.contains(k) { m[k] } else { 0 }",
        "}",
        "fn plain(m: Map<Plain, i64>, k: Plain) -> i64 without panic {",
        "if m.contains(k) { m[k] } else { 0 }",
        "}",
    ];
    let expected = ["6: a key needs a type whose `Eq` and `Hash` are structural"];
    assert_eq!(needs(&lines), expected);
}

/// facts.counting-loops and facts.closest-rule: loops that count, and what the counting loop needs
/// of the others.
#[test]
fn counting_loops() {
    let lines = [
        "fn ok(i: i64) -> bool { i < 10 }",
        "fn loops(n: i64, lo: i64, s: i64) -> i64 without div {",
        "var i = 0",
        "while i < n && ok(i) { if i == 3 { break }",
        "i += 1 }",
        "var hi = n",
        "while hi > lo { hi -= 1 }",
        "while i < n { if ok(i) { i += 1 } }",
        "var m = n",
        "while i < m { i += 1",
        "m += 1 }",
        "while i < n { i += s }",
        "while i != n { i += 1 }",
        "while ok(i) && i < n { i += 1 }",
        "while i < n { if ok(i) { continue }",
        "i += 1 }",
        "while i < n { i += 1",
        "i = i * 2 }",
        "while n > 0 {}",
        "loop { break }",
        "i",
        "}",
    ];
    let expected = [
        "8: a counting loop needs a statement `i += s` of the loop's own block, with `s` known positive",
        "10: a counting loop needs a bound that the loop doesn't change, which line 11 does",
        "12: a counting loop needs a statement `i += s` of the loop's own block, with `s` known positive",
        "13: a counting loop needs a comparison by `<`, `<=`, `>` or `>=`",
        "14: a counting loop needs a comparison by `<`, `<=`, `>` or `>=`",
        "15: a counting loop needs no `continue` before `i += 1`, which line 15 is",
        "17: a counting loop needs `i` written nowhere else, which line 18 does",
        "19: a counting loop needs a `var` on one side",
        "20: a counting loop needs a comparison by `<`, `<=`, `>` or `>=`",
    ];
    assert_eq!(needs(&lines), expected);
}

/// facts.shrinking-recursion and facts.closest-rule: self-calls that shrink, and what shrinking
/// recursion needs of the others.
#[test]
fn recursion() {
    let lines = [
        "fn count(n: i64) -> i64 without div { if n > 0 { 1 + count(n - 1) } else { 0 } }",
        "fn walk(i: i64, n: i64) -> i64 without div { if i < n { walk(i + 1, n) } else { i } }",
        "fn zero(n: i64) -> i64 without div { if n == 0 { 0 } else { zero(n - 1) } }",
        "fn away(n: i64) -> i64 without div { if n > 0 { away(n + 1) } else { 0 } }",
        "fn apart(a: i64, b: i64) -> i64 without div {",
        "if a > 0 && b > 0 { apart(a - 1, b) + apart(a, b - 1) } else { 0 }",
        "}",
    ];
    let expected = [
        "3: shrinking recursion needs a test that gives `n > b` at the self-call on line 3",
        "4: shrinking recursion needs a test that gives `n < b` at the self-call on line 4",
        "6: shrinking recursion needs every self-call to pass `p - s` or `p + s` at one parameter",
    ];
    assert_eq!(needs(&lines), expected);
}
