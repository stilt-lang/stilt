(* Tests of the checks on try and catch in phases 2 and 3 of checking a body
   (errors.phases): marking (effects.marking and effects.result), the arms a catch needs
   (effects.catch) and the reasons catch-alls give (effects.catch-alls-need-reason). Each test prints a
   program's diagnostics as conformance.diagnostic-lines compares them, warnings included. *)

open Diagnostics

let errors =
  "type E = | Bad(str) | Worse\nfn parse(s: str) -> i64 / raise<E> = ?\n"

(* effects.marking *)
let%expect_test "a call that can raise is marked with try" =
  main (errors ^ "fn f(s: str) -> i64 / raise<E> {\nparse(s)\n}");
  [%expect {|
    main.lt:2: W0300
    main.lt:4: E0505
    |}];
  main (errors ^ "fn f(s: str) -> i64 / raise<E> {\ntry parse(s)\n}");
  [%expect {| main.lt:2: W0300 |}];
  (* [raise] is explicit. *)
  main "fn f() / raise<str> {\nraise \"no\"\n}";
  [%expect {| ok |}]

(* effects.marking *)
let%expect_test "a try outside a closure marks the calls inside it" =
  main
    (errors
   ^ "fn f(xs: List<str>) -> List<i64> / raise<E> {\n\
      try xs.map(|l| parse(l))\n\
      }\n\
      fn g(xs: List<str>) -> List<i64> / raise<E> {\n\
      xs.map(|l| try parse(l))\n\
      }");
  [%expect {|
    main.lt:2: W0300
    main.lt:7: E0505 |}]

(* effects.marking *)
let%expect_test "a catch's arms need their own try" =
  main
    (errors
   ^ "fn f(s: str) -> i64 / raise<E> {\n\
      try parse(s) catch _ because \"retry\" => parse(\"0\")\n\
      }\n\
      fn g(s: str) -> i64 / raise<E> {\n\
      try parse(s) catch _ because \"retry\" => try parse(\"0\")\n\
      }");
  [%expect {|
    main.lt:2: W0300
    main.lt:4: E0505 |}]

(* effects.marking, tests: a closure that raises, called after its catch *)
let%expect_test "a raising closure is marked where it is called" =
  main
    (errors
   ^ "fn f(s: str) -> i64 / raise<E> {\n\
      let g = try (|| parse(s)) catch _ because \"none\" => || 0\n\
      g()\n\
      }");
  [%expect {|
    main.lt:2: W0300
    main.lt:5: E0505 |}]

(* effects.empty-try and effects.result *)
let%expect_test "a try with nothing to mark gets a warning" =
  main "fn f(r: Result<i64, str>) -> Result<i64, str> {\ntry r\n}";
  [%expect {| main.lt:2: W0500 |}];
  (* A [catch] whose operand raises nothing: its arms get no warning of
     their own. *)
  main "fn f(x: i64) -> i64 {\ntry x catch _ => 0\n}";
  [%expect {| main.lt:2: W0500 |}];
  main
    "fn f(x: i64) -> i64 {\n\
     try { if x < 0 { raise \"neg\" }\n\
     x } catch _ because \"0\" => 0\n\
     }";
  [%expect {| ok |}]

(* effects.catch-alls-need-reason and effects.reasons-only-on-catch-alls *)
let%expect_test "a catch-all gives a reason or raises again" =
  main
    (errors
   ^ "fn f(s: str) -> i64 / raise<str> {\n\
      let a = try parse(s) catch _ => 0\n\
      let b = try parse(s) catch e => 1\n\
      let c = try parse(s) catch e because \"default\" => 2\n\
      let d = try parse(s) catch e => raise \"failed\"\n\
      let g = try parse(s) catch { e => { let m = 1\n\
      raise \"failed\" } }\n\
      let h = try parse(s) catch { Bad(_) => 3, Worse => 4 }\n\
      a + b + c + d + g + h\n\
      }");
  [%expect {|
    main.lt:2: W0300
    main.lt:4: W0501
    main.lt:5: W0501 |}]

(* effects.catch-alls-need-reason and effects.reasons-only-on-catch-alls *)
let%expect_test "a catch-all that uses its error needs no reason" =
  main
    (errors
   ^ "fn f(s: str) -> Result<i64, E> {\n\
      let a = try parse(s) catch e => return Err(e)\n\
      let b = try parse(s) catch e => [1].map(|x| [e].len() + x)[0]\n\
      let c = try parse(s) catch e => \"{e}\".len()\n\
      let d = try parse(s) catch e => { let e = 0\n\
      e }\n\
      let g = try parse(s) catch e => [1].map(|e| e).len()\n\
      Ok(a + b + c + d + g)\n\
      }");
  [%expect {|
    main.lt:2: W0300
    main.lt:7: W0501
    main.lt:9: W0501 |}]

(* effects.catch *)
let%expect_test "a catch's arms cover its error type" =
  main (errors ^ "fn f(s: str) -> i64 {\ntry parse(s) catch { Bad(_) => 1 }\n}");
  [%expect {|
    main.lt:2: W0300
    main.lt:4: E0329 |}]

(* effects.catch-around-row-variables: the failures of a non-escaping parameter, and of a row
   variable, belong to the caller. *)
let%expect_test "a catch handles no raise of a row variable" =
  main
    (errors
   ^ "fn a(f: fn() -> i64) -> i64 {\n\
      try f() catch _ because \"none\" => 0\n\
      }\n\
      fn b(s: str, f: fn() -> i64) -> i64 {\n\
      try { let n = parse(s)\n\
      f() } catch _ because \"none\" => 0\n\
      }\n\
      fn c(f: fn() -> i64 / raise<E>) -> i64 {\n\
      try f() catch _ because \"none\" => 0\n\
      }\n\
      fn d<e>(escaping f: fn() -> i64 / e) -> fn() -> i64 / e {\n\
      try (|| f()) catch _ because \"none\" => || 0\n\
      }\n\
      fn g(f: fn() -> i64) -> i64 {\n\
      try (try f() catch _ because \"none\" => 0) catch _ because \"none\" => 1\n\
      }\n\
      fn h(xs: List<i64>, f: fn(i64) -> i64) -> List<i64> {\n\
      try xs.map(f) catch _ because \"none\" => []\n\
      }");
  (* [d]'s operand only makes a closure, so it raises nothing (effects.marking). *)
  [%expect
    {|
    main.lt:2: W0300
    main.lt:4: E0506
    main.lt:8: E0506
    main.lt:14: W0500
    main.lt:17: E0506
    main.lt:20: E0506 |}]

(* effects.catch *)
let%expect_test "an empty catch handles only Never" =
  main
    (errors
   ^ "fn a(s: str) -> i64 {\n\
      try parse(s) catch {}\n\
      }\n\
      fn b(x: i64) -> i64 {\n\
      try x catch {}\n\
      }");
  [%expect {|
    main.lt:2: W0300
    main.lt:4: E0329
    main.lt:7: W0500 |}]

(* patterns.unreachable-arms; effects.catch-alls-need-reason *)
let%expect_test "an unreachable catch-all gets one warning" =
  main
    (errors
   ^ "fn f(s: str) -> i64 {\n\
      try parse(s) catch { _ because \"all\" => 0, e => 1 }\n\
      }");
  [%expect {|
    main.lt:2: W0300
    main.lt:4: W0301 |}]
