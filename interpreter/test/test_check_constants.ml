(* Tests of type checking against the rules on constants (declarations.constant-declarations and declarations.constant-expressions), and of where a cycle among declarations is reported (errors.primary-spans).
   Each test prints a program's errors as conformance.diagnostic-lines compares them, leaving out
   warnings. *)

open Diagnostics.Errors

(* declarations.constant-declarations and declarations.constant-expressions *)
let%expect_test "a constant's value is a constant expression" =
  main
    "type P = { x: i64 }\n\
     const ORIGIN: P = P { x: -1 }\n\
     const XS: List<(i64, Option<str>)> = [(1, Some(\"a\")), (2, None)]\n\
     impl P { const UNIT: P = P { x: ORIGIN.x } }";
  [%expect {| main.lt:4: E0326 |}];
  main
    "fn g() -> i64 { 1 }\n\
     const A: i64 = g()\n\
     const B: str = \"{A}\"\n\
     type P = {}\n\
     impl P {\n\
     const C: i64 = 1\n\
     const D: i64 = P.C\n\
     }";
  [%expect {|
    main.lt:2: E0326
    main.lt:3: E0326
    |}]

(* declarations.constant-cycles *)
let%expect_test "constants don't refer to each other in a cycle" =
  main
    "const A: i64 = B\n\
     const B: i64 = A\n\
     const C: (i64, i64) = (1, C.0)\n\
     type T = {}\n\
     impl T {\n\
     const X: i64 = D\n\
     }\n\
     const D: i64 = T.X\n\
     const E: i64 = A";
  [%expect
    {|
    main.lt:2: E0327
    main.lt:3: E0327
    main.lt:3: E0326
    main.lt:8: E0327
    |}];
  main "const C: i64 = C";
  [%expect {| main.lt:1: E0327 |}]

(* errors.primary-spans *)
let%expect_test "a cycle is reported at the declaration that names refer to" =
  main "type A = { a: A }\ntype A = { x: i64 }";
  [%expect {|
    main.lt:1: E0309
    main.lt:2: E0208
    |}];
  main "const A: i64 = A\nconst A: i64 = 1";
  [%expect {|
    main.lt:1: E0327
    main.lt:2: E0208
    |}]
