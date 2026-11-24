(* Tests of the rule that a non-escaping parameter, and a closure literal that
   names one, may only be called or passed on (effects.non-escaping-parameters and effects.no-escape), checked in
   phase 2 (errors.phases). Each test prints a program's diagnostics. *)

open Diagnostics

let%expect_test "a non-escaping parameter may be called and passed on" =
  main
    "fn twice(x: i64, f: fn(i64) -> i64) -> i64 { f(f(x)) }\n\
     fn on(xs: List<i64>, f: fn(i64) -> i64) -> List<i64> {\n\
     xs.map(f).map(|x| twice(x, f))\n\
     }\n\
     fn now(f: fn()) { (|| f())() }";
  [%expect {| ok |}]

let%expect_test "each way of keeping a parameter is an error" =
  main
    "type B = { f: fn() }\n\
     fn stored(f: fn()) -> B { B { f } }\n\
     fn listed(f: fn()) -> List<fn()> { [f] }\n\
     fn returned(f: fn()) -> fn() { f }\n\
     fn bound(f: fn()) { let g = f\n\
     g() }\n\
     fn id<T>(x: T) -> T { x }\n\
     fn given(f: fn()) { id(f)() }\n\
     fn valued(f: fn(), h: fn(fn())) { h(f) }\n\
     fn closure(f: fn()) -> fn() { || f() }";
  [%expect
    {|
    main.lt:2: E0508
    main.lt:3: E0508
    main.lt:4: E0508
    main.lt:5: E0508
    main.lt:8: E0508
    main.lt:9: E0508
    main.lt:10: E0508
    |}]

let%expect_test "a parameter that escapes twice gets one error" =
  main "fn twice(f: fn(), g: fn()) -> (fn(), fn(), fn()) {\n(|| g(),\nf, f)\n}";
  [%expect {|
    main.lt:2: E0508
    main.lt:3: E0508
    |}]

let%expect_test "an escaping parameter, or one passed inout, may be kept" =
  main
    "type B = { f: fn() / io }\n\
     fn stored(escaping f: fn() / io) -> B { B { f } }\n\
     fn swapped(inout f: fn()) -> fn() { f }";
  [%expect {| ok |}]
