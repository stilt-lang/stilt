(* Tests of exhaustiveness in phases 2 and 3 of checking a body (errors.phases): a match covers every value, and an arm that can never match gets a
   warning (patterns.match, patterns.unreachable-arms and patterns.non-exhaustive-matches). Each test prints a program's diagnostics as
   conformance.diagnostic-lines compares them, warnings included. *)

open Diagnostics

(* patterns.algorithm and patterns.non-exhaustive-matches *)
let%expect_test "a match covers every value" =
  main
    "type Color = | Red | Green | Blue\n\
     fn a(c: Color) -> i64 {\n\
     match c { Red => 1, Green => 2 }\n\
     }\n\
     fn b(c: Color) -> i64 {\n\
     match c { Red => 1, Green | Blue => 2 }\n\
     }\n\
     fn c(o: Option<bool>) -> i64 {\n\
     match o { None => 0, Some(true) => 1 }\n\
     }\n\
     fn d(t: (bool, ())) -> i64 {\n\
     match t { (true, ()) => 1, (false, _) => 2 }\n\
     }";
  [%expect {|
    main.lt:3: E0329
    main.lt:9: E0329 |}]

(* patterns.algorithm *)
let%expect_test "lists have one constructor per length" =
  main
    "fn a(xs: List<i64>) -> i64 {\n\
     match xs { [] => 0, [x] => x, [x, y, ..] => x + y }\n\
     }\n\
     fn b(xs: List<i64>) -> i64 {\n\
     match xs { [] => 0, [x, y, ..] => x + y }\n\
     }\n\
     fn c(xs: List<i64>) -> i64 {\n\
     match xs { [x, ..rest] => x, [] => 0 }\n\
     }\n\
     fn d(xs: List<i64>) -> i64 {\n\
     match xs { [_, _] => 2, [_] => 1 }\n\
     }";
  [%expect {|
    main.lt:5: E0329
    main.lt:11: E0329 |}]

(* patterns.algorithm *)
let%expect_test "numbers and strings need a catch-all" =
  main
    "fn a(n: i64) -> i64 {\n\
     match n { 0 => 1, 1 => 2 }\n\
     }\n\
     fn b(s: str) -> i64 {\n\
     match s { \"a\" => 1, _ => 2 }\n\
     }\n\
     fn c(x: f64) -> i64 {\n\
     match x { y => 1 }\n\
     }\n\
     fn d(b: bool) -> i64 {\n\
     match b { true => 1, false => 0 }\n\
     }";
  [%expect {| main.lt:2: E0329 |}]

(* patterns.guards-and-constants *)
let%expect_test "guards and constants cover nothing" =
  main
    "const ZERO: i64 = 0\n\
     type Color = | Red | Green\n\
     const RED: Color = Red\n\
     const GREEN: Color = Green\n\
     fn a(n: i64) -> i64 {\n\
     match n { x if x > 0 => 1, x if x <= 0 => 0 }\n\
     }\n\
     fn b(c: Color) -> i64 {\n\
     match c { RED => 1, GREEN => 2 }\n\
     }\n\
     fn c(n: i64) -> i64 {\n\
     match n { ZERO => 0, _ => 1 }\n\
     }";
  [%expect {|
    main.lt:6: E0329
    main.lt:9: E0329 |}]

(* patterns.empty-matches *)
let%expect_test "a match on Never needs no arms" =
  main "fn a(n: Never) -> i64 {\nmatch n {}\n}";
  [%expect {| ok |}]

(* patterns.unreachable-arms *)
let%expect_test "an arm that can never match gets a warning" =
  main
    "const ONE: i64 = 1\n\
     type Color = | Red | Green\n\
     fn a(n: i64) -> i64 {\n\
     match n { _ => 1, 4 => 2 }\n\
     }\n\
     fn b(c: Color) -> i64 {\n\
     match c { Red | Green => 1, Red => 2 }\n\
     }\n\
     fn c(t: (bool, bool)) -> i64 {\n\
     match t { (true, _) => 1, (_, true) => 2, (false, false) => 3, (true, \
     true) => 4 }\n\
     }\n\
     fn d(n: i64) -> i64 {\n\
     match n { ONE => 1, x if x > 2 => 2, _ => 3, ONE => 4 }\n\
     }\n\
     fn e(n: i64) -> i64 {\n\
     match n { ONE => 1, 1 => 2, _ => 3 }\n\
     }";
  [%expect
    {|
    main.lt:4: W0301
    main.lt:7: W0301
    main.lt:10: W0301
    main.lt:13: W0301 |}]

(* patterns.algorithm *)
let%expect_test "constructors that build no value aren't needed" =
  main
    "type Empty = | Gone(Never)\n\
     fn a(o: Option<Never>) -> i64 {\n\
     match o { None => 0 }\n\
     }\n\
     fn b(o: Option<Never>) -> i64 {\n\
     match o { None => 0, Some(_) => 1 }\n\
     }\n\
     fn c(r: Result<i64, Never>) -> i64 {\n\
     match r { Ok(n) => n }\n\
     }\n\
     fn d(e: Empty) -> i64 {\n\
     match e {}\n\
     }\n\
     fn g(o: Option<Empty>) -> i64 {\n\
     match o { None => 0 }\n\
     }";
  [%expect {| main.lt:6: W0301 |}]

(* patterns.non-exhaustive-matches and patterns.unreachable-arms; errors.broken-parts *)
let%expect_test "patterns on parts with errors cause nothing more" =
  main
    "type T = | A(Unknown) | B\n\
     type R = { a: Unknown, b: bool }\n\
     fn f(t: T) -> i64 {\n\
     match t { A(Some(_)) => 0, A(x) => 1, B => 2 }\n\
     }\n\
     fn g(r: R) -> i64 {\n\
     match r { R { a: 1, b: true } => 0, R { a: _, b: false } => 1 }\n\
     }\n\
     fn h(t: T) -> i64 {\n\
     match t { A(Some(_)) => 0, B => 1 }\n\
     }\n\
     fn k(t: T) -> i64 {\n\
     match t { A(K1(5)) => 0, _ => 1 }\n\
     }";
  [%expect
    {|
    main.lt:1: E0211
    main.lt:2: E0211
    main.lt:13: E0211 |}]

(* patterns.algorithm and patterns.unreachable-arms *)
let%expect_test "an or-pattern over every constructor is a wildcard" =
  main
    ("fn f(t: (bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, \
      bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, \
      bool, bool, bool, bool, bool, bool, bool, bool)) -> i64 {\n\
      match t {\n" ^ "("
    ^ String.concat ", " (List.init 30 (fun _ -> "true | false"))
    ^ ") => 1\n_ => 2\n}\n}");
  [%expect {| main.lt:4: W0301 |}]
