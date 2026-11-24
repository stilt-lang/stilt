(* Tests of the rules of acceptance (facts.rules-of-acceptance and facts.closest-rule): what E0204 says
   the closest rule needs of each operation that none proves, with the
   compiler's own tests (compiler/stilt-types/src/accept/tests.rs), which
   hold the same programs and the same messages. Each test prints a program's
   errors, an E0204 as its line and what its rule needs. *)

open Stilt

let needs lines =
  let text = String.concat "\n" lines in
  let errors =
    List.filter Diagnostic.is_error
      (Driver.check (Diagnostics.sources [ ("main.lt", text) ]))
  in
  if errors = [] then print_endline "ok";
  List.iter
    (fun (d : Diagnostic.t) ->
      let marker = "`: " in
      let rec need i =
        if i + String.length marker > String.length d.message then None
        else if String.sub d.message i (String.length marker) = marker then
          Some (String.sub d.message (i + 3) (String.length d.message - i - 3))
        else need (i + 1)
      in
      match need 0 with
      | Some n when d.code = Code.e0204 -> Printf.printf "%d: %s\n" d.line n
      | _ -> Printf.printf "%d: %s %s\n" d.line (d.code :> string) d.message)
    errors

(* facts.range-loops: indexes that range loops prove. *)
let%expect_test "range loops accept" =
  needs
    [
      "fn total(xs: List<i64>) -> i64 without panic {";
      "var s = 0";
      "for i in 0..xs.len() { s += xs[i] }";
      "for i in 0..xs.len() - 1 { s += xs[i] + xs[i + 1] }";
      "for i in 1..xs.len() { s += xs[i - 1] }";
      "var ys = xs";
      "for i in 0..ys.len() { ys[i] = s }";
      "s + ys[0] * 0";
      "}";
    ];
  [%expect {|
    8: a guard needs a test that gives `0 < ys.len()`
    |}]

(* facts.closest-rule: what the range loop needs, in the order facts.range-loops lists it. *)
let%expect_test "range loops need" =
  needs
    [
      "fn upto(xs: List<i64>, n: i64) -> i64 without panic {";
      "var s = 0";
      "for i in 0..n { s += xs[i] }";
      "for i in n..xs.len() { s += xs[i] }";
      "for i in 0..xs.len() - 1 { s += xs[i + 2] }";
      "for i in 1..xs.len() { s += xs[i - 2] }";
      "for i in 0..=xs.len() { s += xs[i] + xs[2 * i] }";
      "for i in 0..xs.len() { let at = || xs[i]";
      "s += at() }";
      "s";
      "}";
      "fn pushed(xs: List<i64>) -> List<i64> without panic {";
      "var ys = xs";
      "for i in 0..ys.len() {";
      "ys[i] = 1";
      "ys.push(0)";
      "}";
      "ys";
      "}";
    ];
  [%expect
    {|
    3: a range loop needs it to end at `xs.len()`, not at `n`
    4: a range loop needs it to start at a value known non-negative
    5: a range loop needs it to end at `xs.len() - 2`, not at `xs.len() - 1`
    6: a range loop needs it to start at `2` or above
    7: a range loop needs it to end at `xs.len()`, not at `..=xs.len()`
    8: a range loop needs the index outside closures
    15: a range loop needs a body that keeps the length of `ys`, which line 16 changes
    |}]

(* facts.guards: indexes that guards prove, the sieve's among them. *)
let%expect_test "guards accept" =
  needs
    [
      "fn at(xs: List<i64>, i: i64) -> i64 without panic {";
      "if i >= 0 && i < xs.len() { return xs[i] }";
      "if 0 <= i { if xs.len() > i { return xs[i] } }";
      "if !xs.is_empty() { return xs[0] }";
      "if i < 0 || i >= xs.len() { return 0 }";
      "xs[i]";
      "}";
      "fn sieve(m: i64) -> List<bool> without panic, div {";
      "var flags = []";
      "for _ in 0..m + 1 { flags.push(true) }";
      "for i in 2..flags.len() {";
      "var k = i + i";
      "while k < flags.len() {";
      "flags[k] = false";
      "k += i";
      "}";
      "}";
      "flags";
      "}";
    ];
  [%expect {| ok |}]

(* facts.closest-rule: what the guard needs, in the order facts.guards lists it. *)
let%expect_test "guards need" =
  needs
    [
      "fn at(xs: List<i64>, ys: List<i64>, i: i64, n: i64) -> i64 without \
       panic {";
      "var zs = xs";
      "var j = i";
      "if j >= 0 && j < zs.len() { zs[j] = { j = 5; 1 } }";
      "if i >= 0 && i < zs.len() {";
      "let _ = zs.pop()";
      "return zs[i]";
      "}";
      "if i < xs.len() { return xs[i] }";
      "if i >= 0 && i < ys.len() { return xs[i] }";
      "if i >= 0 && i + 1 < xs.len() { return xs[i + 1] }";
      "if xs[i] > 0 && i >= 0 && i < xs.len() { return 1 }";
      "xs[n * i]";
      "}";
    ];
  [%expect
    {|
    4: a guard needs nothing between the test and the index to write `j`, which line 4 does
    7: a guard needs nothing between the test and the index to change the length of `zs`, which line 6 does
    9: a guard needs a test that gives `i >= 0`
    10: a guard needs a test that gives `i < xs.len()`
    11: a guard needs the index to be a name or a literal
    12: a guard needs a test that gives `i >= 0`
    13: a guard needs the index to be a name or a literal
    |}]

(* facts.divisors and facts.closest-rule: divisions that divisors prove, and what the divisor needs of the others. *)
let%expect_test "divisors" =
  needs
    [
      "const TEN: i64 = 10";
      "fn ratio(n: i64, d: i64, e: i64) -> i64 without panic {";
      "var s = n / 2 + n % TEN";
      "if d != 0 { s += n / d }";
      "if 0 > d { s += n / d }";
      "if d == 0 { return s }";
      "for k in 1..10 { s += n / k }";
      "s += n / d";
      "var f = e";
      "if f != 0 {";
      "f -= 1";
      "s += n / f";
      "}";
      "if e - 1 != 0 { s += n / (e - 1) }";
      "s + n / e";
      "}";
    ];
  [%expect
    {|
    12: a divisor needs nothing between the test and the division to write `f`, which line 11 does
    14: a divisor needs to be a name or a literal other than 0
    15: a divisor needs a test that gives `e != 0`
    |}]

(* facts.keys and facts.closest-rule: reads of keys that keys prove, and what the key needs of the others. *)
let%expect_test "keys" =
  needs
    [
      "fn touch(inout m: Map<str, i64>) without panic { m[\"z\"] = 0 }";
      "fn name() -> str { \"a\" }";
      "fn counts(words: List<str>, j: str, k0: str) -> i64 without panic {";
      "var m: Map<str, i64> = Map.new()";
      "for w in words {";
      "if !m.contains(w) { m[w] = 0 }";
      "m[w] += 1";
      "}";
      "var k = k0";
      "m.insert(k, 1)";
      "m[j] = 2";
      "var s = m[k] + m[\"z\"]";
      "k = \"b\"";
      "s += m[k]";
      "m[k] = 1";
      "let _ = m.remove(j)";
      "s += m[k]";
      "m[name()] = 1";
      "s += m[name()] + m[\"{k}\"]";
      "m[\"a\"] = 1";
      "touch(inout m)";
      "s + m[\"a\"]";
      "}";
    ];
  [%expect
    {|
    12: a key needs a test that gives `m.contains("z")`, or a store of `"z"` before it
    14: a key needs nothing between to write `k`, which line 13 does
    17: a key needs nothing between to change `m` but by storing into it, which line 16 does
    19: a key needs to be a name or a literal that doesn't interpolate
    22: a key needs nothing between to change `m` but by storing into it, which line 21 does
    |}]

(* facts.keys: a key's type has an `Eq` and a `Hash` structural throughout its parts, so a record with impls of its own isn't one, while the same record without them is. *)
let%expect_test "keys of records" =
  needs
    [
      "type Own = { n: i64 }";
      "impl Eq for Own { fn eq(self, o: Own) -> bool { self.n == o.n } }";
      "impl Hash for Own { fn hash(self) -> u64 { self.n.hash() } }";
      "type Plain = { n: i64 }";
      "fn own(m: Map<Own, i64>, k: Own) -> i64 without panic {";
      "if m.contains(k) { m[k] } else { 0 }";
      "}";
      "fn plain(m: Map<Plain, i64>, k: Plain) -> i64 without panic {";
      "if m.contains(k) { m[k] } else { 0 }";
      "}";
    ];
  [%expect {| 6: a key needs a type whose `Eq` and `Hash` are structural |}]

(* facts.counting-loops and facts.closest-rule: loops that count, and what the counting loop needs of the others. *)
let%expect_test "counting loops" =
  needs
    [
      "fn ok(i: i64) -> bool { i < 10 }";
      "fn loops(n: i64, lo: i64, s: i64) -> i64 without div {";
      "var i = 0";
      "while i < n && ok(i) { if i == 3 { break }";
      "i += 1 }";
      "var hi = n";
      "while hi > lo { hi -= 1 }";
      "while i < n { if ok(i) { i += 1 } }";
      "var m = n";
      "while i < m { i += 1";
      "m += 1 }";
      "while i < n { i += s }";
      "while i != n { i += 1 }";
      "while ok(i) && i < n { i += 1 }";
      "while i < n { if ok(i) { continue }";
      "i += 1 }";
      "while i < n { i += 1";
      "i = i * 2 }";
      "while n > 0 {}";
      "loop { break }";
      "i";
      "}";
    ];
  [%expect
    {|
    8: a counting loop needs a statement `i += s` of the loop's own block, with `s` known positive
    10: a counting loop needs a bound that the loop doesn't change, which line 11 does
    12: a counting loop needs a statement `i += s` of the loop's own block, with `s` known positive
    13: a counting loop needs a comparison by `<`, `<=`, `>` or `>=`
    14: a counting loop needs a comparison by `<`, `<=`, `>` or `>=`
    15: a counting loop needs no `continue` before `i += 1`, which line 15 is
    17: a counting loop needs `i` written nowhere else, which line 18 does
    19: a counting loop needs a `var` on one side
    20: a counting loop needs a comparison by `<`, `<=`, `>` or `>=`
    |}]

(* facts.shrinking-recursion and facts.closest-rule: self-calls that shrink, and what shrinking recursion needs of the others. *)
let%expect_test "recursion" =
  needs
    [
      "fn count(n: i64) -> i64 without div { if n > 0 { 1 + count(n - 1) } \
       else { 0 } }";
      "fn walk(i: i64, n: i64) -> i64 without div { if i < n { walk(i + 1, n) \
       } else { i } }";
      "fn zero(n: i64) -> i64 without div { if n == 0 { 0 } else { zero(n - 1) \
       } }";
      "fn away(n: i64) -> i64 without div { if n > 0 { away(n + 1) } else { 0 \
       } }";
      "fn apart(a: i64, b: i64) -> i64 without div {";
      "if a > 0 && b > 0 { apart(a - 1, b) + apart(a, b - 1) } else { 0 }";
      "}";
    ];
  [%expect
    {|
    3: shrinking recursion needs a test that gives `n > b` at the self-call on line 3
    4: shrinking recursion needs a test that gives `n < b` at the self-call on line 4
    6: shrinking recursion needs every self-call to pass `p - s` or `p + s` at one parameter
    |}]
