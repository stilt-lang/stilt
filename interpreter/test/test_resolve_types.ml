(* Tests of name resolution in types and rows: a generic type takes all its
   type arguments (declarations.type-arguments), and a row holds each kind of element once
   (effects.repeated-elements). Each test prints a program's diagnostics as conformance.diagnostic-lines
   compares them: a file, a line and a code. *)

open Diagnostics

(* declarations.type-arguments *)
let%expect_test "generic types take all their type arguments" =
  main "fn f(a: List<i64>, b: Map<str, List<i64>>, c: Option<(i64, str)>) {}";
  [%expect {| ok |}];
  main
    "type W<T> = {}\n\
     impl<T> W<T> { fn g(x: Self<i64>) {} }\n\
     fn f<T>(a: List, b: Option<i64, i64>, c: T<i64>) {}";
  [%expect
    {|
    main.lt:2: E0300
    main.lt:3: E0300
    main.lt:3: E0300
    main.lt:3: E0300
    |}]

(* effects.rows, and facts.implicit-effects *)
let%expect_test "rows hold each kind of element once" =
  main "fn f<e>(escaping g: fn() / {io, e}) / {io, raise<str>, e} {}";
  [%expect {| ok |}];
  (* effects.row-variables: a non-escaping parameter writes no row variable. *)
  main "fn f<e>(g: fn() / e, h: fn(fn() / {io, e})) {}";
  [%expect {|
    main.lt:1: E0509
    main.lt:1: E0509
    |}];
  main
    "fn f<e, g>() / {io,\n\
     io} {}\n\
     fn h() / {raise<str>, raise<\n\
     i64>} {}\n\
     fn k<e, g>() / {e,\n\
     g} {}";
  [%expect
    {|
    main.lt:2: E0500
    main.lt:3: E0500
    main.lt:6: E0500
    |}];
  main "fn f() / panic {}\nfn g<alloc>() / alloc {}\nfn h<io>() {}";
  [%expect
    {|
    main.lt:1: E0501
    main.lt:2: E0501
    main.lt:3: E0501
    |}]
