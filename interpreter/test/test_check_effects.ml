(* Tests of type checking against the rules on effects (effects.rows and effects.function-values): the row that
   a body's effects fit, the rows that a function value fits, and the one error
   type that code raises. Each test prints a program's errors as conformance.diagnostic-lines
   compares them, leaving out warnings. *)

open Diagnostics.Errors

(* effects.catch-alls-need-reason and effects.reasons-only-on-catch-alls *)
let%expect_test "only a catch-all gives a reason" =
  main
    "fn g() -> i64 / raise<Option<i64>> { raise None }\n\
     fn f() -> i64 {\n\
     try g() catch {\n\
     Some(x) because \"x\" => x\n\
     None => 0\n\
     }\n\
     }\n\
     fn h() -> i64 {\n\
     try g() catch e because \"any\" => 0\n\
     }";
  [%expect {| main.lt:4: E0504 |}]

(* effects.missing-effects *)
let%expect_test "a body's effects fit its row" =
  main "fn f() {\nprint(\"a\")\nprint(\"b\")\n}";
  [%expect {| main.lt:2: E0502 |}];
  main "fn f() -> i64 {\nraise \"no\"\n}";
  [%expect {| main.lt:2: E0502 |}];
  main
    "fn apply<e>(escaping h: fn() / e) {\n\
     h()\n\
     }\n\
     fn apply2<e>(escaping h: fn() / e) / e { h() }";
  [%expect {| main.lt:2: E0502 |}];
  (* A non-escaping parameter's effects are in the function's own row
     (effects.non-escaping-parameters). *)
  main "fn apply(h: fn()) {\nh()\n}\nfn both(f: fn(), g: fn()) { f()\ng() }";
  [%expect {| ok |}];
  (* A closure's effects are part of its type, not of the body that
     creates it. *)
  main "fn f() {\nlet g = || print(\"a\")\n}";
  [%expect {| ok |}];
  (* A [catch] handles the raise, and the other effects pass through
     (effects.non-escaping-parameters). *)
  main
    "fn g() -> i64 / {io, raise<str>} { 0 }\n\
     fn f() -> i64 {\n\
     try g() catch _ because \"none\" => 0\n\
     }";
  [%expect {| main.lt:3: E0502 |}]

(* effects.function-values *)
let%expect_test "a function value fits a larger row where it meets one" =
  main
    "fn run(h: fn() / io) / io { h() }\n\
     fn quiet() {}\n\
     fn f() / io { run(quiet) }\n\
     fn runs(hs: List<fn() / io>) {}\n\
     fn g() { runs([quiet]) }\n\
     fn h(hs: List<fn()>) {\n\
     runs(hs)\n\
     }";
  [%expect {| main.lt:7: E0311 |}];
  (* Branches and elements have the union of their rows, whatever their
     order. *)
  main
    "fn quiet() {}\n\
     fn loud() / io { print(\"x\") }\n\
     fn runs(hs: List<fn() / io>) {}\n\
     fn f(c: bool) / io {\n\
     let a = if c { quiet } else { loud }\n\
     let b = [quiet, loud]\n\
     runs(b)\n\
     a()\n\
     }";
  [%expect {| ok |}]

(* effects.one-error-type *)
let%expect_test "code raises one error type" =
  main
    "fn a() / raise<str> { raise \"a\" }\n\
     fn b() / raise<i64> { raise 1 }\n\
     fn f() / raise<str> {\n\
     try a()\n\
     try b()\n\
     }\n\
     fn g() {\n\
     try {\n\
     try a()\n\
     try b()\n\
     } catch _ because \"none\" => ()\n\
     }";
  [%expect {|
    main.lt:5: E0503
    main.lt:10: E0503
    |}]

(* program.test-results and program.doc-examples *)
let%expect_test "tests and examples raise errors that can be shown" =
  main
    "fn g() / raise<str> { raise \"x\" }\n\
     test \"raises\" {\n\
     try g()\n\
     }\n\
     /// ex: double(2) == 4\n\
     fn double(x: i64) -> i64 { x * 2 }";
  [%expect {| ok |}];
  main
    "type E = { f: fn() }\n\
     fn g() / raise<E> { raise E { f: || () } }\n\
     test \"raises\" {\n\
     try g()\n\
     }\n\
     /// ex: double(2)\n\
     fn double(x: i64) -> i64 { x * 2 }";
  [%expect {|
    main.lt:3: E0318
    main.lt:6: E0311
    |}]

(* effects.function-values *)
let%expect_test "an inout argument's type is the parameter's exactly" =
  main
    "fn swap_in(inout f: fn() / io) { f = || print(\"x\") }\n\
     fn pure_call(f: fn()) { f() }\n\
     fn main() {\n\
     var h: fn() = || ()\n\
     swap_in(inout h)\n\
     pure_call(h)\n\
     }";
  [%expect {| main.lt:5: E0311 |}]

(* effects.missing-effects *)
let%expect_test "each row reports its own missing effects" =
  main
    "fn apply(escaping f: fn()) { f() }\n\
     fn g() {\n\
     print(\"b\")\n\
     apply(|| print(\"a\"))\n\
     }";
  [%expect {|
    main.lt:3: E0502
    main.lt:4: E0502
    |}];
  (* A non-escaping parameter passes the closure's effects through to the
     call, where the row already reported `io` (effects.non-escaping-parameters). *)
  main
    "fn apply(f: fn()) { f() }\n\
     fn g() {\n\
     print(\"b\")\n\
     apply(|| print(\"a\"))\n\
     }";
  [%expect {| main.lt:3: E0502 |}]

(* effects.inference and effects.non-escaping-parameters *)
let%expect_test "effects that an open row gains later reach every row it fits" =
  main "fn f() {\nlet k = |g| g()\nk(|| print(\"x\"))\n}";
  [%expect {| main.lt:3: E0502 |}];
  main
    "fn pure(h: fn()) { h() }\n\
     fn f() {\n\
     let k = |g| g()\n\
     pure(|| k(|| print(\"x\")))\n\
     }";
  [%expect {| main.lt:4: E0502 |}];
  (* The catch learns the raise of a function value called later. *)
  main "fn f() -> str {\nlet k = |g| try g() catch e => e\nk(|| raise 5)\n}";
  [%expect {| main.lt:3: E0311 |}];
  (* A join keeps rows apart that only meet through a row variable. *)
  main
    "fn f<e>(escaping g: fn() / e) / {raise<List<fn() / e>>, e} {}\n\
     fn h() {\n\
     let j = if true { |g| g() } else { f }\n\
     let n: i64 = j\n\
     }";
  [%expect {| main.lt:4: E0311 |}]

(* effects.missing-effects *)
let%expect_test "a second error type is reported once per row" =
  main "fn f(c: bool) / raise<i64> {\nif c {\nraise \"a\"\n}\nraise \"b\"\n}";
  [%expect {| main.lt:3: E0503 |}]
