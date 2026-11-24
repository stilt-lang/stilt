(* Tests of the rules on declarations that need no function body: impls
   (traits.impl-blocks), records that contain themselves (declarations.recursive-types) and the
   signature of main (program.main). Each test prints a program's
   diagnostics as conformance.diagnostic-lines compares them. *)

open Diagnostics

(* traits.bounded-blocks *)
let%expect_test "inherent impls live in their type's home module" =
  check
    [
      ("main.lt", "use shapes\nimpl shapes.Shape {\nfn f() {}\n}");
      ("shapes.lt", "pub type Shape = | Dot\nimpl Shape { fn g() {} }");
    ];
  [%expect {| main.lt:2: E0301 |}];
  main "impl i64 { fn twice(self) -> i64 { self } }";
  [%expect {| main.lt:1: E0301 |}]

(* traits.impl-blocks and traits.orphan-rule *)
let%expect_test "an impl's type is its constructor applied to its parameters" =
  main
    "type Pair<A, B> = { a: A, b: B }\n\
     impl<A, B> Pair<A, B> {}\n\
     impl<B, A> Pair<A, B> {}\n\
     impl Pair<i64, i64> {}\n\
     impl<A> Pair<A, A> {}\n\
     impl<A, B, C> Pair<A, B> {}\n\
     impl (i64, i64) {}";
  [%expect
    {|
    main.lt:4: E0302
    main.lt:5: E0302
    main.lt:6: E0302
    main.lt:7: E0302
    |}]

(* traits.orphan-rule *)
let%expect_test "an impl lives with its trait or its type" =
  check
    [
      ( "main.lt",
        "use a\n\
         use b\n\
         impl a.Named for b.Thing {\n\
         fn name(self) -> str { \"\" }\n\
         }" );
      ("a.lt", "pub trait Named { fn name(self) -> str }");
      ("b.lt", "pub type Thing = {}");
    ];
  [%expect {| main.lt:3: E0303 |}];
  check
    [
      ( "main.lt",
        "use a\n\
         type Thing = {}\n\
         impl a.Named for Thing {\n\
         fn name(self) -> str { \"\" }\n\
         }" );
      ("a.lt", "pub trait Named { fn name(self) -> str }");
    ];
  [%expect {| ok |}]

let%expect_test "a trait has one impl per type" =
  main
    "trait Named { fn name(self) -> str }\n\
     type Thing = {}\n\
     impl Named for Thing { fn name(self) -> str { \"a\" } }\n\
     impl Named for Thing { fn name(self) -> str { \"b\" } }";
  [%expect {| main.lt:4: E0304 |}]

let%expect_test "an impl holds exactly the trait's methods, with its signatures"
    =
  main
    "trait Shape {\n\
     fn area(self) -> f64\n\
     fn name(self) -> str { \"shape\" }\n\
     }\n\
     type Square = { side: f64 }\n\
     impl Shape for Square {\n\
     fn perimeter(self) -> f64 { 0.0 }\n\
     }";
  [%expect {|
    main.lt:6: E0305
    main.lt:7: E0306
    |}];
  main
    "trait Shape {\n\
     fn area(self) -> f64\n\
     fn scale<T: Ord>(inout self, by: T) / io\n\
     }\n\
     type Square = { side: f64 }\n\
     impl Shape for Square {\n\
     fn area(self) -> f64 { self.side }\n\
     fn scale<U: Ord>(inout self, by: U) / io {}\n\
     }\n\
     type Circle = { r: f64 }\n\
     impl Shape for Circle {\n\
     fn area(inout self) -> f64 { 0.0 }\n\
     fn scale<U: Show>(inout self, by: U) / io {}\n\
     }";
  [%expect {|
    main.lt:12: E0307
    main.lt:13: E0307
    |}];
  (* Bounds are traits, not names (traits.bounds). *)
  check
    [
      ( "main.lt",
        "use a\n\
         use b\n\
         trait T { fn m<X: a.Tr>(self, x: X) }\n\
         type U = {}\n\
         impl T for U { fn m<X: b.Tr>(self, x: X) {} }" );
      ("a.lt", "pub trait Tr { fn go(self) }");
      ("b.lt", "pub trait Tr { fn go(self) }");
    ];
  [%expect {| main.lt:5: E0307 |}];
  (* [Self] in the trait is the impl's type. *)
  main
    "trait Same { fn same(self, other: Self) -> bool }\n\
     type T = {}\n\
     impl Same for T { fn same(self, other: T) -> bool { true } }";
  [%expect {| ok |}]

(* traits.method-resolution *)
let%expect_test "an inherent method doesn't share a name with a trait method" =
  main
    "trait Named { fn name(self) -> str }\n\
     type Thing = {}\n\
     impl Thing { fn name(self) -> str { \"\" } }\n\
     impl Named for Thing { fn name(self) -> str { \"\" } }";
  [%expect {| main.lt:4: E0308 |}];
  (* Structural impls count too (traits.structural-impls). *)
  main "type Point = { x: i64 }\nimpl Point {\nfn show(self) -> str { \"\" }\n}";
  [%expect {| main.lt:3: E0308 |}];
  main
    "type Callback = { f: fn() }\n\
     impl Callback { fn show(self) -> str { \"\" } }";
  [%expect {| ok |}]

(* declarations.recursive-types *)
let%expect_test "a record can't contain itself directly" =
  main
    "type Node = { next: Node }\n\
     type A = { b: (i64, B) }\n\
     type B = { a: A }\n\
     type Box<T> = { item: T }\n\
     type C = { boxed: Box<C> }";
  [%expect
    {|
    main.lt:1: E0309
    main.lt:3: E0309
    main.lt:5: E0309
    |}];
  (* Through a generic record, however its arguments nest. *)
  main
    "type Pair<T> = { a: T, b: i64 }\n\
     type A = { p: Pair<i64>, q: Pair<A> }\n\
     type Box<T> = { item: T }\n\
     type C = { b: Box<Box<C>> }";
  [%expect {|
    main.lt:2: E0309
    main.lt:4: E0309
    |}];
  main
    "type List2 = { next: Option<List2> }\n\
     type Tree = { children: List<Tree> }\n\
     type Lazy = { make: fn() -> Lazy }";
  [%expect {| ok |}]

(* program.missing-main *)
let%expect_test "main takes nothing, returns () and raises a showable error" =
  main "fn main() / {io, raise<str>} {}";
  [%expect {| ok |}];
  main "fn main(args: List<str>) {}";
  [%expect {| main.lt:1: E0310 |}];
  main "fn main() -> i64 { 0 }";
  [%expect {| main.lt:1: E0310 |}];
  main "fn main<e>() / e {}";
  [%expect {| main.lt:1: E0310 |}];
  main "fn main() / raise<fn()> {}";
  [%expect {| main.lt:1: E0310 |}];
  (* Only the root module's main is the entry point. *)
  check [ ("main.lt", ""); ("tools.lt", "fn main(x: i64) {}") ];
  [%expect {| ok |}]
