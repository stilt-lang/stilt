(* Tests of names that clash: each name is defined once in its namespace
   (declarations.unique-names), and the names of the prelude and of primitive types are
   taken (program.prelude-names). Most tests print a program's
   diagnostics as conformance.diagnostic-lines compares them: a file, a line and a code. *)

open Diagnostics
open Resolved

(* declarations.unique-names *)
let%expect_test "each name is defined once in its namespace" =
  main "type UserId = | UserId(i64)\nfn f() -> UserId { UserId(1) }";
  [%expect {| ok |}];
  main "fn f() {}\nfn f() {}";
  [%expect {| main.lt:2: E0208 |}];
  main "type A = | V\ntype B = | V";
  [%expect {| main.lt:2: E0208 |}];
  main "type T = {}\ntrait T {}";
  [%expect {| main.lt:2: E0208 |}];
  main "use std.fs\nfn fs() {}";
  [%expect {| main.lt:2: E0208 |}];
  main "test \"a\" {}\ntest \"a\" {}";
  [%expect {| main.lt:2: E0208 |}];
  main
    "type R = { a: i64,\n\
    \ a: i64 }\n\
     fn f<T,\n\
    \ T>(x: i64,\n\
    \ x: i64) {}\n\
     fn g() { let (y,\n\
    \ y) = (1, 2) }";
  [%expect
    {|
    main.lt:2: E0208
    main.lt:4: E0208
    main.lt:5: E0208
    main.lt:7: E0208
    |}];
  main "trait Tr {\nfn m(self)\nfn m(self)\n}";
  [%expect {| main.lt:3: E0208 |}];
  main "type T = {}\nimpl T { fn f() {} }\nimpl T {\nfn f() {}\n}";
  [%expect {| main.lt:4: E0208 |}]

(* traits.bounded-blocks *)
let%expect_test "a function's generics don't reuse its impl block's" =
  main "type W<T> = {}\nimpl<T> W<T> {\nfn f<U>(x: U) {}\nfn g<T>(x: T) {}\n}";
  [%expect {| main.lt:4: E0208 |}]

(* program.prelude-names, and lexical.primitive-type-names *)
let%expect_test "prelude and primitive type names are taken" =
  main "fn print() {}\ntype Option = {}\ntype Maybe = | Some(i64) | Nothing";
  [%expect
    {|
    main.lt:1: E0209
    main.lt:2: E0209
    main.lt:3: E0209
    |}];
  main "fn str() {}\ntype T = { i64: i64 }\nfn f(bool: i64) { let f32 = 1 }";
  [%expect
    {|
    main.lt:1: E0210
    main.lt:2: E0210
    main.lt:3: E0210
    main.lt:3: E0210
    |}];
  (* A local may reuse a prelude function's name. *)
  main "fn f() { let print = 1 }";
  [%expect {| ok |}];
  (* A name clashes only in its own namespace. *)
  main
    "type Token = | Eq | List(List<i64>) | Map\n\
     type Less = { by: i64 }\n\
     trait Some { fn some(self) -> bool }\n\
     fn same<T: Eq>(a: T, b: T) -> bool { Eq.eq(a, b) }\n\
     fn f() -> Map<str, i64> { Map.new() }";
  [%expect {| ok |}]

let%expect_test
    "uses of a name that clashes with the prelude have the error type" =
  main
    "type Option = { value: i64 }\n\
     type Eq = {}\n\
     type List = {}\n\
     fn f(x: Option<i64>, y: List<i64>) {}\n\
     fn g<T: Eq>() {}\n\
     fn h() { let _ = Option { value: 1 } }";
  [%expect
    {|
    main.lt:1: E0209
    main.lt:2: E0209
    main.lt:3: E0209
    |}];
  refers "fn print(n: i64) {}\nfn t() { print }";
  [%expect {| error |}]
