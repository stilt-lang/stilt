(* Tests of the order of the phases of checking a body (errors.phases): each
   runs only on the bodies that the earlier ones found no error in. Each test
   prints a program's diagnostics as conformance.diagnostic-lines compares them, warnings
   included. *)

open Diagnostics

(* errors.error-type *)
let%expect_test "later phases run only on bodies with no earlier error" =
  (* Two errors of phase 2 in one body are both reported. *)
  main
    "type Color = | Red | Green\n\
     fn f(c: Color) {\n\
     var xs = [1]\n\
     for x in xs { xs.push(x) }\n\
     match c { Red => () }\n\
     }";
  [%expect {|
    main.lt:4: E0404
    main.lt:5: E0329 |}];
  (* An error of phase 1 hides the body's later errors and warnings. *)
  main
    "type Color = | Red | Green\n\
     fn f(c: Color) {\n\
     let n: i64 = \"one\"\n\
     match c { Red => () }\n\
     let t = try 1\n\
     }\n\
     fn g() -> i64 = ?";
  [%expect {|
    main.lt:3: E0311
    main.lt:7: W0300 |}];
  (* An error of phase 2 hides the body's warnings. *)
  main
    "type Color = | Red | Green\n\
     fn f(c: Color) -> i64 {\n\
     let t = try 2\n\
     match c { Red => t }\n\
     }";
  [%expect {| main.lt:4: E0329 |}]

(* errors.error-type *)
let%expect_test "a name resolution error in a body ends its checking" =
  main
    "type C = | A(i64) | B(i64)\n\
     fn f(c: C) -> i64 {\n\
     let (a, a) = (1, 2)\n\
     let k = 1\n\
     k = 2\n\
     match c { A(_) => 1 }\n\
     }\n\
     fn g(c: C) -> i64 {\n\
     let n = match c { A(x) | B(y) => 1 }\n\
     ?\n\
     }";
  [%expect {|
    main.lt:3: E0208
    main.lt:9: E0217 |}]
