(* Tests of type checking against the rules on anonymous and open records
   (records.anonymous-types and records.record-bounds) and variadic generics (variadics.packs), beyond the conformance suite's:
   record bounds in impls and [where] clauses, updates and patterns of bounded
   parameters, and the inference of packs. Each test prints a program's errors
   as conformance.diagnostic-lines compares them, leaving out warnings. *)

open Diagnostics.Errors

(* records.anonymous-types and records.anonymous-literals: the same type in any order, and never a declared
   record. *)
let%expect_test "anonymous record types" =
  main
    "fn f(p: { a: i64, b: str }) -> { b: str, a: i64 } { p }\n\
     fn g() -> { a: i64 } { { a: 1, b: 2 } }\n\
     fn h() -> { a: i64, b: str } { { b: \"x\", a: 1 } }";
  [%expect {| main.lt:2: E0311 |}]

(* records.record-bounds: a record bound on an impl's parameter, beside a trait. *)
let%expect_test "record bounds" =
  main
    "type W<P> = { inner: P }\n\
     impl<P: { name: str, .. }> W<P> {\n\
     fn name(self) -> str { self.inner.name }\n\
     }\n\
     fn shown<P: { age: i64, .. } + Show>(p: P) -> str { \"{p} {p.age}\" }\n\
     fn ok() -> str { shown({ age: 1, tag: true }) }\n\
     fn missing<P: { age: i64, .. }>(p: P) -> str { p.name }";
  [%expect {| main.lt:7: E0313 |}]

(* records.bound-fields: the field's type is the bound's exactly, which inference
   gives a literal. *)
let%expect_test "a bound's field types" =
  main
    "type Box<T> = { v: T }\n\
     fn small<B: { v: u8, .. }>(b: B) -> u8 { b.v }\n\
     fn ok() -> u8 { small(Box { v: 7 }) }\n\
     fn wide() -> u8 { small(Box { v: 300 }) }\n\
     fn wrong() -> u8 { small({ v: true }) }";
  [%expect {|
    main.lt:4: E0320
    main.lt:5: E0318
    |}]

(* records.anonymous-patterns and records.update *)
let%expect_test "updates and patterns of bounded parameters" =
  main
    "fn aged<P: { age: i64, .. }>(p: P) -> P { { ..p, age: p.age + 1 } }\n\
     fn named<P: { age: i64, .. }>(p: P) -> P { { ..p, name: \"x\" } }\n\
     fn age<P: { age: i64, .. }>(p: P) -> i64 { let { age } = p\n\
     age }";
  [%expect {|
    main.lt:2: E0313
    main.lt:3: E0316
    |}]

(* records.update: a declared record's update names it. *)
let%expect_test "a declared record's update" =
  main
    "type P = { a: i64 }\n\
     fn f(p: P) -> P { { ..p, a: 1 } }\n\
     fn g(p: P) -> P { P { ..p } }";
  [%expect {| main.lt:2: E0311 |}]

(* variadics.packs and variadics.pack-tuples: a pack's bounds, of traits and of records, hold for
   each element, and a pack tuple is never indexed. *)
let%expect_test "a pack's bounds" =
  main
    "fn ages<..Ts: { age: i64, .. }>(xs: (..Ts)) -> List<i64> { [..xs.age] }\n\
     fn ok() -> List<i64> { ages(({ age: 1 }, { age: 2, tag: true })) }\n\
     fn bad() -> List<i64> { ages(({ age: 1 }, 3)) }\n\
     fn shown<..Ts: Show>(xs: (..Ts)) -> str { \"{xs}\" }\n\
     fn f() {}\n\
     fn unshown() -> str { shown((1, f, \"x\")) }\n\
     fn first<..Ts>(xs: (..Ts)) -> i64 { xs[0] }";
  [%expect
    {|
    main.lt:3: E0318
    main.lt:6: E0318
    main.lt:7: E0342
    |}]

(* variadics.packs: a pack where none may be is E0344 alone, and a plain type
   parameter after it, written spread or not. *)
let%expect_test "misplaced packs report only E0344" =
  main
    "fn f(g: fn<..X>(X) -> i64) -> i64 { 0 }\n\
     fn h(g: fn<..X>((..X)) -> i64) -> i64 { 0 }\n\
     trait T<..Ts> { fn get(self) -> (..Ts) }\n\
     type Early<..Ts, U> = { a: (..Ts), b: Ts, c: U }\n\
     type Two<..Ts, ..Us> = { a: (..Ts), b: Us }";
  [%expect
    {|
    main.lt:1: E0344
    main.lt:2: E0344
    main.lt:3: E0344
    main.lt:4: E0344
    main.lt:5: E0344
    |}]

(* variadics.pack-inference: a pack from a tuple's elements, a function's parameters,
   and another pack, one element longer. *)
let%expect_test "inferring packs" =
  main
    "fn apply<..Ts, R>(f: fn(..Ts) -> R, args: (..Ts)) -> R { f(..args) }\n\
     fn plus(a: i64, b: i64) -> i64 { a + b }\n\
     fn named() -> i64 { apply(plus, (1, 2)) }\n\
     fn arity() -> i64 { apply(plus, (1,)) }\n\
     fn grow<..Ts>(xs: (..Ts)) -> (i64, ..Ts) { (0, ..xs) }\n\
     fn grown() -> (i64, str) { grow((\"a\",)) }";
  [%expect {| main.lt:4: E0311 |}]

(* variadics.spread-expressions: a raise inside a spread passes through, and [try] marks
   the calls in it. *)
let%expect_test "effects in a spread" =
  main
    "fn get<T>(xs: List<T>) -> T / raise<str> { xs.first() else raise \
     \"empty\" }\n\
     fn heads<..Ts>(xs: (..List<Ts>)) -> (..Ts) / raise<str> { (..try get(xs)) }\n\
     fn unmarked<..Ts>(xs: (..List<Ts>)) -> (..Ts) / raise<str> { (..get(xs)) }";
  [%expect {| main.lt:3: E0505 |}]
