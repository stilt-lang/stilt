(* Tests of shared writes in phase 2 of checking a body (errors.phases):
   which copies a body makes and how long they last (modes.escaping and modes.not-escaping and
   6), and which modifications they make shared (modes.shared-writes), as
   [without copy] reports them (facts.copy and facts.without-copy). Each test prints a
   program's errors as conformance.diagnostic-lines compares them. *)

open Diagnostics.Errors

(* modes.copies and modes.shared-writes *)
let%expect_test "a copy bound by a let lasts until its scope ends" =
  main
    "fn bound() -> List<i64> without copy {\n\
     var ys = [1]\n\
     let k = ys\n\
     ys[0] = 2\n\
     k\n\
     }\n\
     fn ended() -> List<i64> without copy {\n\
     var ys = [1]\n\
     if true { let k = ys\n\
     assert k.len() == 1 }\n\
     ys[0] = 2\n\
     ys\n\
     }\n\
     fn replaced() -> List<i64> without copy {\n\
     var ys = [1]\n\
     let k = ys\n\
     ys = [2]\n\
     ys[0] = 3\n\
     k\n\
     }";
  (* [ended]'s copy ends with its block, and [replaced]'s write comes after
     an assignment of the whole binding. *)
  [%expect {| main.lt:4: E0204 |}]

(* modes.copies and modes.shared-writes *)
let%expect_test "a copy of a copy is a copy of the binding" =
  main
    "fn chained() -> List<i64> without copy {\n\
     var ys = [1]\n\
     let kept = {\n\
     let k = ys\n\
     k\n\
     }\n\
     ys[0] = 2\n\
     kept\n\
     }";
  [%expect {| main.lt:7: E0204 |}]

(* modes.escaping and modes.copies *)
let%expect_test "a copy stored in a value lasts while the value can" =
  main
    "fn escaped(c: bool) -> List<List<i64>> without copy {\n\
     var ys = [1]\n\
     if c {\n\
     let both = [ys]\n\
     if c { return both }\n\
     }\n\
     ys[0] = 2\n\
     [ys]\n\
     }\n\
     fn kept(c: bool) -> List<i64> without copy {\n\
     var ys = [1]\n\
     if c {\n\
     let both = [ys]\n\
     assert both.len() == 1\n\
     }\n\
     ys[0] = 2\n\
     ys\n\
     }";
  (* [both] escapes in [escaped], so the copy it stores lasts for the rest
     of the function. *)
  [%expect {| main.lt:7: E0204 |}]

(* modes.copies and modes.shared-writes, and values.consumed-parameters *)
let%expect_test "a call that loses the reuse of its argument copies it" =
  main
    "fn keep(xs: List<i64>) -> List<i64> { xs }\n\
     fn lost() -> i64 without copy {\n\
     var ys = [1]\n\
     let k = keep(ys)\n\
     ys[0] = 2\n\
     k.len() + ys.len()\n\
     }\n\
     fn reused() -> i64 without copy {\n\
     var ys = [1]\n\
     ys[0] = 2\n\
     let k = keep(ys)\n\
     k.len()\n\
     }\n\
     fn read() -> i64 without copy {\n\
     var ys = [1]\n\
     let n = ys.len()\n\
     ys[0] = 2\n\
     n + ys.len()\n\
     }";
  [%expect {| main.lt:5: E0204 |}]

(* modes.not-escaping, modes.copies and modes.shared-writes *)
let%expect_test "closures, patterns and inout parameters" =
  main
    "fn captured() -> i64 without copy {\n\
     var ys = [1]\n\
     let f = || ys.len()\n\
     ys[0] = 2\n\
     f()\n\
     }\n\
     fn parts(p: (List<i64>, List<i64>)) -> (List<i64>, List<i64>) without \
     copy {\n\
     var q = p\n\
     match q {\n\
     (a, _) => {\n\
     q.1[0] = 1\n\
     q.0[0] = 2\n\
     assert a.len() == 1\n\
     }\n\
     }\n\
     q\n\
     }\n\
     fn param(inout xs: List<i64>) -> List<i64> without copy {\n\
     let k = xs\n\
     xs.push(1)\n\
     k\n\
     }";
  (* The pattern copies [q.0], so writing [q.1] shares nothing. *)
  [%expect
    {|
    main.lt:4: E0204
    main.lt:12: E0204
    main.lt:20: E0204 |}]

(* modes.shared-writes: the copy that [k] holds lasts into the next turn, the
   one that a binding of the body holds ends with its turn. *)
let%expect_test "a loop whose body makes a copy shares its writes" =
  main
    "fn looped() -> i64 without copy {\n\
     var ys = [1]\n\
     var k = [0]\n\
     var n = 0\n\
     for i in 0..2 {\n\
     ys[0] = i\n\
     k = ys\n\
     n += k.len()\n\
     }\n\
     n\n\
     }\n\
     fn turned() -> i64 without copy {\n\
     var ys = [1]\n\
     var n = 0\n\
     for i in 0..2 {\n\
     ys[0] = i\n\
     let k = ys\n\
     n += k.len()\n\
     }\n\
     n\n\
     }";
  [%expect {| main.lt:6: E0204 |}]
