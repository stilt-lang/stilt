(* Tests of exclusivity in phase 2 of checking a body (errors.phases): what
   may be modified, and when (modes.what-can-be-modified and modes.durations). Each test prints a program's
   diagnostics as conformance.diagnostic-lines compares them, warnings included. *)

open Diagnostics

(* modes.overlapping-inout *)
let%expect_test "one call modifies overlapping places" =
  main
    "type Pair = { a: i64, b: i64 }\n\
     impl Pair {\n\
     fn bump(inout self, inout n: i64) {}\n\
     }\n\
     fn swap(inout x: i64, inout y: i64) {}\n\
     fn put(inout p: Pair, inout n: i64) {}\n\
     fn f() {\n\
     var p = Pair { a: 1, b: 2 }\n\
     var n = 0\n\
     swap(inout n, inout n)\n\
     put(inout p, inout p.a)\n\
     p.bump(inout p.b)\n\
     swap(inout p.a, inout p.b)\n\
     }";
  [%expect
    {|
    main.lt:10: E0402
    main.lt:11: E0402
    main.lt:12: E0402 |}]

(* modes.overlapping-inout *)
let%expect_test "a for loop's place can't change while it runs" =
  main
    "type Cart = { items: List<i64>, total: i64 }\n\
     impl Cart {\n\
     fn clear(inout self) {}\n\
     }\n\
     fn add(inout xs: List<i64>) {}\n\
     fn f() {\n\
     var cart = Cart { items: [1], total: 0 }\n\
     var other = [2]\n\
     for i in cart.items {\n\
     cart.items.push(i)\n\
     add(inout cart.items)\n\
     cart.clear()\n\
     cart.items[0] = 1\n\
     cart.total = i\n\
     other.push(i)\n\
     }\n\
     for (k, x) in other.enumerate(0) {\n\
     other.push(x)\n\
     }\n\
     }";
  [%expect
    {|
    main.lt:10: E0404
    main.lt:11: E0404
    main.lt:12: E0404
    main.lt:13: E0404 |}]

(* modes.durations and modes.overlapping-inout *)
let%expect_test "arguments that are read end before the call" =
  main
    "fn f(inout a: i64, b: i64) {}\n\
     fn g() {\n\
     var xs = [1]\n\
     xs.push(xs.len())\n\
     xs.push(xs[0])\n\
     var a = 1\n\
     f(inout a, a)\n\
     }";
  [%expect {| ok |}]

(* modes.what-can-be-modified, and expressions.capture *)
let%expect_test "only var bindings and inout parameters change" =
  main
    "fn f(n: i64, xs: List<i64>, inout ys: List<i64>) {\n\
     n = 1\n\
     xs.push(1)\n\
     ys.push(1)\n\
     let k = 1\n\
     k += 1\n\
     for x in ys { x = 2 }\n\
     match n { m => { m = 3 } }\n\
     var v = 1\n\
     let g = || { v = 2 }\n\
     var w = xs\n\
     w.push(1)\n\
     var xs = xs\n\
     xs.push(2)\n\
     }";
  [%expect
    {|
    main.lt:2: E0403
    main.lt:3: E0403
    main.lt:6: E0403
    main.lt:7: E0403
    main.lt:8: E0403
    main.lt:10: E0403 |}]
