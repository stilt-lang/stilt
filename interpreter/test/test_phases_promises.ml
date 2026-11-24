(* Tests of the checked promises in phase 2 of checking a body (errors.phases): updates in place under [without alloc] (facts.writes-in-place, facts.in-place-parameters and facts.copy-at-call) and
   termination under [without div] (facts.div, facts.descending-self-calls and facts.without-div). Each test prints a
   program's errors as conformance.diagnostic-lines compares them. *)

open Diagnostics.Errors

(* facts.own-storage and facts.writes-in-place *)
let%expect_test "a binding holds its own storage after its last assignment" =
  main
    "fn literal() -> List<i64> without alloc {\n\
     var ys = [0]\n\
     ys[0] = 1\n\
     ys\n\
     }\n\
     fn looped(xs: List<i64>) -> i64 without alloc {\n\
     var n = 0\n\
     for _ in 0..2 {\n\
     var ys = xs\n\
     ys[0] = 1\n\
     n += ys[0]\n\
     }\n\
     n\n\
     }\n\
     fn taken(xs: List<i64>) -> List<i64> without alloc {\n\
     var ys = xs\n\
     var zs = ys\n\
     zs[0] = 1\n\
     zs\n\
     }";
  (* [looped] takes [xs] in a loop that its declaration is outside of, so
     the use isn't its last; the literal of [literal] allocates itself. *)
  [%expect {|
    main.lt:2: E0204
    main.lt:10: E0204 |}]

(* facts.in-place-parameters and facts.copy-at-call *)
let%expect_test "storage reaches a callee's in-place parameter" =
  main
    "fn set(inout xs: List<i64>) without alloc { xs[0] = 1 }\n\
     fn via(xs: List<i64>) -> List<i64> without alloc {\n\
     var ys = xs\n\
     set(inout ys)\n\
     ys\n\
     }\n\
     fn outer(xs: List<i64>) -> List<i64> without alloc { via(xs) }\n\
     fn caller() -> List<i64> without alloc {\n\
     var ys = outer(outer([]))\n\
     set(inout ys)\n\
     ys\n\
     }";
  (* [via] puts [xs] in place through [ys], so [outer]'s argument [xs]
     reaches it too. In [caller], the literal allocates itself but goes to
     [outer] as it is; the outer call's argument isn't a binding, so the call
     copies it, and [ys] holds a call's result, not its own storage. *)
  [%expect {|
    main.lt:9: E0204
    main.lt:10: E0204
    |}]

(* projections.writable-views, and facts.writes-in-place *)
let%expect_test "a view writes in place only storage of its own" =
  main
    "use std.view\n\
     fn own(inout xs: List<i64>) without alloc {\n\
     var v = view.into(inout xs, 0, 1)\n\
     v[0] = 1\n\
     }\n\
     fn shared(inout xs: List<i64>) -> List<i64> without alloc {\n\
     let k = xs\n\
     var v = view.into(inout xs, 0, 1)\n\
     v[0] = 1\n\
     k\n\
     }";
  [%expect {| main.lt:8: E0204 |}]

(* facts.div and facts.descending-self-calls *)
let%expect_test "recursion ends when it descends into one parameter" =
  main
    "type Tree = | Leaf | Node(Tree, i64, Tree)\n\
     fn left(t: Tree, n: i64) -> i64 without div {\n\
     if let Node(l, _, _) = t { left(l, n + 1) } else { n }\n\
     }\n\
     fn swapped(a: Tree, b: Tree) -> i64 without div {\n\
     match a {\n\
     Leaf => 0\n\
     Node(l, _, _) => swapped(b, l) + swapped(l, b)\n\
     }\n\
     }\n\
     fn held(t: Tree) -> i64 without div {\n\
     match t {\n\
     Leaf => 0\n\
     Node(l, _, _) => {\n\
     let again = l\n\
     held(again)\n\
     }\n\
     }\n\
     }";
  (* [swapped] passes a part of [a] in each position once, but neither
     position gets one at every self-call. *)
  [%expect {| main.lt:8: E0204 |}]

(* facts.div and facts.without-div *)
let%expect_test "what may not end is inherited, and limited functions end" =
  main
    "fn waits() { while false {} }\n\
     fn calls() without div { waits() }\n\
     fn ends() without div {}\n\
     fn ok() without div { ends() }\n\
     fn values(fs: List<fn() -> i64>) -> i64 without div {\n\
     var n = 0\n\
     for f in fs { n += f() }\n\
     n\n\
     }";
  (* A function value that a pattern binds is held by a local binding. *)
  [%expect {|
    main.lt:2: E0204
    main.lt:7: E0204 |}]
