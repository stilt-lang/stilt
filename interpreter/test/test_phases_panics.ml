(* Tests of implicit effects in phase 2 of checking a body (errors.phases):
   which operations can panic (effects.panicking-operations), and the check that code limited by
   [without panic] has none (effects.panicking-operations and effects.without-panic). Each test prints a program's diagnostics as
   conformance.diagnostic-lines compares them, warnings included. *)

open Diagnostics

let limited = "module main\nwithout panic\n"

(* effects.panicking-operations and effects.without-panic *)
let%expect_test "a module without panic has no operation that can panic" =
  main
    (limited
   ^ "fn at(xs: List<i64>, i: i64) -> i64 { xs[i] }\n\
      fn div(a: i64, b: i64) -> i64 { a / b }\n\
      fn rem(inout a: i64, b: i64) { a %= b }\n\
      fn fdiv(a: f64, b: f64) -> f64 { a / b }\n\
      fn add(a: i64) -> i64 { a + 1 }\n\
      fn cut(s: str) -> str { s.slice(0, 1) }\n\
      fn boom() { panic(\"x\") }\n\
      fn check(b: bool) { assert b }\n\
      fn todo() -> i64 = ?\n\
      fn put(inout m: Map<str, i64>) { m[\"a\"] = 1 }\n\
      fn bump(inout m: Map<str, i64>) { m[\"a\"] += 1 }\n\
      test \"tests may assert\" { assert 1 == 1 }");
  [%expect
    {|
    main.lt:3: E0204
    main.lt:4: E0204
    main.lt:5: E0204
    main.lt:8: E0204
    main.lt:9: E0204
    main.lt:10: E0204
    main.lt:11: E0204
    main.lt:13: E0204 |}]

(* effects.without-panic; facts.inference and facts.calls-through-function-values *)
let%expect_test "panics are inherited from other modules" =
  check
    [
      ( "main.lt",
        "use lib\n\
         fn main() {}\n\
         fn f(xs: List<i64>) -> i64 { lib.first(xs) }\n\
         fn g(xs: List<i64>) -> i64 { lib.safe(xs) }\n\
         fn h(f: fn(i64) -> i64) -> i64 { f(1) }\n\
         fn k() -> i64 { h(lib.share) }" );
      ( "lib.lt",
        "module lib\n\
         pub fn first(xs: List<i64>) -> i64 { xs[0] }\n\
         pub fn safe(xs: List<i64>) -> i64 { xs.len() }\n\
         pub fn share(n: i64) -> i64 { 100 / n }\n\
         pub fn deep(xs: List<i64>) -> i64 { first(xs) }" );
      ( "pure.lt",
        "module pure\n\
         without panic\n\
         use lib\n\
         fn a(xs: List<i64>) -> i64 { lib.deep(xs) }\n\
         fn b(xs: List<i64>) -> i64 { lib.safe(xs) }\n\
         fn c() -> fn(i64) -> i64 { lib.share }\n\
         fn d(f: fn(i64) -> i64) -> i64 { f(1) }\n\
         fn e(xs: List<i64>) -> i64 { xs.map(|x| 100 / x).len() }\n\
         fn g(xs: List<i64>) -> i64 { a(xs) }" );
    ];
  [%expect {|
    pure.lt:4: E0204
    pure.lt:6: E0204
    pure.lt:8: E0204 |}]

(* facts.inference *)
let%expect_test "a panic in a recursive group is found" =
  check
    [
      ("main.lt", "use lib\nfn main() {}\n");
      ( "lib.lt",
        "module lib\n\
         pub fn even(n: i64) -> bool { if n == 0 { true } else { odd(n - 1) } }\n\
         pub fn odd(n: i64) -> bool { if n == 0 { 1 / n == 0 } else { even(n - \
         1) } }" );
      ( "pure.lt",
        "module pure\nwithout panic\nuse lib\nfn a() -> bool { lib.even(4) }" );
    ];
  [%expect {| pure.lt:4: E0204 |}]

(* facts.inference: trait methods *)
let%expect_test "comparisons name the impls they use" =
  check
    [
      ("main.lt", "use lib\nfn main() {}\n");
      ( "lib.lt",
        "module lib\n\
         pub type Odd = { n: i64 }\n\
         impl Eq for Odd {\n\
         fn eq(self, other: Odd) -> bool { self.n / other.n == 1 }\n\
         }\n\
         impl Ord for Odd {\n\
         fn compare(self, other: Odd) -> Ordering { unreachable() }\n\
         }\n\
         pub type Fine = { n: i64 }" );
      ( "pure.lt",
        "module pure\n\
         without panic\n\
         use lib\n\
         fn a(x: lib.Odd, y: lib.Odd) -> bool { x < y }\n\
         fn b(xs: List<lib.Odd>) -> List<lib.Odd> { xs.sorted() }\n\
         fn c(x: lib.Fine, y: lib.Fine) -> bool { x < y }\n\
         fn d(x: (i64, lib.Odd), y: (i64, lib.Odd)) -> bool { x == y }" );
    ];
  [%expect {|
    pure.lt:4: E0204
    pure.lt:5: E0204
    pure.lt:7: E0204 |}]

(* effects.panicking-operations *)
let%expect_test "a nonzero literal divisor can't panic" =
  main
    (limited
   ^ "fn half(a: i64) -> i64 { a / 2 }\n\
      fn neg(a: i64) -> i64 { a % -3 }\n\
      fn zero(a: i64) -> i64 { a / 0 }\n\
      fn hex(a: i64) -> i64 { a / 0x0 }\n\
      fn by(a: i64, b: i64) -> i64 { a / b }\n\
      fn halve(inout a: i64) { a /= 2 }");
  [%expect {|
    main.lt:5: E0204
    main.lt:6: E0204
    main.lt:7: E0204 |}]

(* effects.without-overflow *)
let%expect_test "a limited module's panics are reported once" =
  check
    [
      ("main.lt", "use lib\nuse pure\nfn main() {}\n");
      ( "base.lt",
        "module base\nwithout panic\npub fn at(xs: List<i64>) -> i64 { xs[0] }"
      );
      ( "lib.lt",
        "module lib\n\
         use base\n\
         pub fn first(xs: List<i64>) -> i64 { base.at(xs) }" );
      ( "pure.lt",
        "module pure\n\
         without panic\n\
         use lib\n\
         pub fn f(xs: List<i64>) -> i64 { lib.first(xs) }" );
    ];
  [%expect {| base.lt:3: E0204 |}]

(* facts.inference; effects.panicking-operations; traits.operators and traits.show *)
let%expect_test "operators and stores name the impl methods they use" =
  check
    [
      ("main.lt", "use lib\nuse pure\nfn main() {}\n");
      ( "lib.lt",
        "module lib\n\
         pub type Key = { n: i64 }\n\
         impl Eq for Key {\n\
         fn eq(self, other: Key) -> bool { self.n == other.n }\n\
         }\n\
         impl Hash for Key {\n\
         fn hash(self) -> u64 { unreachable() }\n\
         }\n\
         pub type Loud = { n: i64 }\n\
         impl Show for Loud {\n\
         fn show(self) -> str { \"loud\" }\n\
         fn show_nested(self) -> str { panic(\"nested\") }\n\
         }\n\
         pub type Odd = { n: i64 }\n\
         impl Eq for Odd {\n\
         fn eq(self, other: Odd) -> bool { true }\n\
         }\n\
         impl Ord for Odd {\n\
         fn compare(self, other: Odd) -> Ordering { unreachable() }\n\
         }\n\
         pub trait Pick {\n\
         fn pick<X: Ord>(self, a: X, b: X) -> bool\n\
         }\n\
         pub type Box = { n: i64 }\n\
         impl Pick for Box {\n\
         fn pick<X: Ord>(self, a: X, b: X) -> bool { a < b }\n\
         }" );
      ( "pure.lt",
        "module pure\n\
         without panic\n\
         use lib\n\
         pub fn store(inout m: Map<lib.Key, i64>, k: lib.Key) { m[k] = 1 }\n\
         pub fn insert(inout m: Map<lib.Key, i64>, k: lib.Key) { m.insert(k, \
         1) }\n\
         pub fn shown(x: lib.Loud) -> str { \"{x}\" }\n\
         pub fn nested(xs: List<lib.Loud>) -> str { \"{xs}\" }\n\
         pub fn equal(a: lib.Odd, b: lib.Odd) -> bool { a == b }\n\
         pub fn picked(b: lib.Box, x: lib.Odd, y: lib.Odd) -> bool { b.pick(x, \
         y) }" );
    ];
  [%expect
    {|
    pure.lt:4: E0204
    pure.lt:5: E0204
    pure.lt:7: E0204
    pure.lt:9: E0204 |}]
