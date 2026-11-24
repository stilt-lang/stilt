(* Tests of type checking against the rules on polymorphic function types and
   lazy values (polymorphism.function-types and polymorphism.instantiation): where such a type may be written, what may be given
   for one, and how each use instantiates it. Each test prints a program's
   errors as conformance.diagnostic-lines compares them, leaving out warnings. *)

open Diagnostics.Errors

let both = "fn both(f: fn<T: Show>(T) -> str) -> str { \"{f(1)} {f(true)}\" }\n"

(* polymorphism.function-types and polymorphism.placement *)
let%expect_test "where a polymorphic function type may be written" =
  main
    "type R = { f: fn<T>(T) -> T }\n\
     type V = | V(fn<T>(T) -> T)\n\
     fn f(g: fn(fn<T>(T) -> T) -> i64) -> i64 { 0 }\n\
     fn g() -> Option<fn<T>(T) -> T> { None }\n\
     fn h(f: fn() -> fn<T>(T) -> T) {}";
  [%expect {|
    main.lt:4: E0340
    main.lt:5: E0340
    |}];
  (* A type parameter that appears only in the row, or only in a bound, is
     used nowhere a call could tell it from. *)
  main
    "fn f(g: fn<T, E>(T) -> T / raise<E>) {}\n\
     fn h(g: fn<T: Eq, U: Ord>(T) -> T) {}";
  [%expect {|
    main.lt:1: E0339
    main.lt:2: E0339
    |}]

(* polymorphism.function-types: its type parameters reuse no name in scope. *)
let%expect_test "a polymorphic function type's own scope" =
  main "fn f<T>(x: T, g: fn<T>(T) -> T) -> T { g(x) }";
  [%expect {| main.lt:1: E0208 |}];
  main "type B<A> = { a: A }\nimpl<A> B<A> {\nfn f(g: fn<A>(A) -> A) {}\n}";
  [%expect {| main.lt:3: E0208 |}];
  main "fn f<T>(x: T, g: fn<U>(U) -> U) -> T { g(x) }";
  [%expect {| ok |}];
  main "fn f(g: fn<T, T>(T) -> T) {}";
  [%expect {| main.lt:1: E0208 |}]

(* polymorphism.instantiation and polymorphism.arguments *)
let%expect_test "what may be given for a polymorphic function type" =
  main
    (both
   ^ "fn shown<A: Show>(a: A) -> str { \"{a}\" }\n\
      fn ok() -> str { both(shown) }\n\
      fn closure() -> str { both(|x| \"<{x}>\") }\n\
      fn local() -> str {\n\
      let g = |x: i64| \"{x}\"\n\
      both(g)\n\
      }");
  [%expect {| main.lt:7: E0311 |}];
  (* A rigid type can't take a type from outside. *)
  main
    "fn apply<A>(f: fn<T>(T) -> A, x: i64) -> A { f(x) }\n\
     fn g() -> i64 {\n\
     apply(|x| x, 1)\n\
     }";
  [%expect {| main.lt:3: E0311 |}]

(* polymorphism.instantiation: each use instantiates afresh, and meets the bounds. *)
let%expect_test "each use of a polymorphic value instantiates it" =
  main
    "fn f(g: fn<T: Ord>(T) -> T) -> List<i64> {\n\
     let s = g(\"a\")\n\
     [1, 2].map(g)\n\
     }\n\
     fn h(g: fn<T: Ord>(T) -> T) -> i64 {\n\
     g(|| 1)()\n\
     }";
  [%expect {| main.lt:6: E0318 |}];
  (* Two polymorphic function types are the same up to renaming. *)
  main
    "fn a(f: fn<A: Show>(A) -> str) -> str { f(1) }\n\
     fn b(g: fn<B: Show>(B) -> str) -> str { a(g) }\n\
     fn c(g: fn<B>(B) -> str) -> str { a(g) }";
  [%expect {| main.lt:3: E0311 |}]

(* polymorphism.lazy-values *)
let%expect_test "a lazy value implements no prelude trait" =
  main
    "use std.lazy\n\
     fn f(a: lazy.Lazy<i64>) -> i64 {\n\
     let n = a.get()\n\
     let s = \"{a}\"\n\
     n\n\
     }";
  [%expect {| main.lt:4: E0318 |}]
