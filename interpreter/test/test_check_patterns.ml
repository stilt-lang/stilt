(* Tests of type checking against the rules on patterns (patterns.pattern-forms and patterns.irrefutable-positions): their
   shapes, the names they bind, the values they match, and where they must be
   irrefutable. Each test prints a program's errors as conformance.diagnostic-lines compares them,
   leaving out warnings. *)

open Diagnostics.Errors

(* patterns.let-else *)
let%expect_test "the else branch of a let-else doesn't finish" =
  main
    "fn f(o: Option<i64>) -> i64 {\n\
     let Some(x) = o else return 0\n\
     let Some(y) = o else 0\n\
     x + y\n\
     }";
  [%expect {| main.lt:3: E0311 |}]

(* patterns.floats *)
let%expect_test "alternatives bind each name with one type" =
  main
    "type T = | A(i64) | B(str)\n\
     fn f(t: T) -> i64 {\n\
     match t {\n\
     A(x) | B(x) => 0\n\
     }\n\
     }";
  [%expect {| main.lt:4: E0311 |}]

(* patterns.floats *)
let%expect_test "a record pattern lists every field or ends with .." =
  main
    "type P = { x: i64, y: i64 }\n\
     fn f(p: P) -> i64 {\n\
     let P { x } = p\n\
     let P { y, .. } = p\n\
     x + y\n\
     }";
  [%expect {| main.lt:3: E0316 |}]

(* patterns.floats *)
let%expect_test "a variant pattern has one pattern per payload field" =
  main
    "fn f(o: Option<i64>) -> i64 {\nmatch o {\nSome(a, b) => a\nNone => 0\n}\n}";
  [%expect {| main.lt:3: E0315 |}]

(* patterns.irrefutable-positions *)
let%expect_test "let, for and closure parameters take irrefutable patterns" =
  main
    "fn f(o: Option<i64>, xs: List<Option<i64>>) {\n\
     let Some(x) = o\n\
     for Some(y) in xs {}\n\
     let g = |Some(z): Option<i64>| z\n\
     }";
  [%expect
    {|
    main.lt:2: E0321
    main.lt:3: E0321
    main.lt:4: E0321
    |}];
  (* A variant of a single-variant type always matches. *)
  main
    "type W = | W(i64)\n\
     fn f(w: W, ps: List<(i64, W)>) -> i64 {\n\
     let W(x) = w\n\
     for (_, W(y)) in ps {}\n\
     x\n\
     }";
  [%expect {| ok |}]

(* patterns.floats *)
let%expect_test "a float isn't matched by a literal or a constant" =
  main
    "const HALF: f64 = 0.5\n\
     type P = { x: f64 }\n\
     const O: P = P { x: 0.0 }\n\
     const N: i64 = 3\n\
     fn f(x: f64, p: P, n: i64) -> i64 {\n\
     let a = match x { HALF => 1, _ => 0 }\n\
     let b = match p { O => 1, _ => 0 }\n\
     let c = match x { 1 => 1, _ => 0 }\n\
     match n { N => 1, -1 => 2, _ => 0 }\n\
     }";
  [%expect
    {|
    main.lt:6: E0328
    main.lt:7: E0328
    main.lt:8: E0328
    |}]
