(* Tests of how type checking goes on after an error (errors.root-causes): each
   error is reported once, causes no other, and hides none. Each test prints a
   program's errors as conformance.diagnostic-lines compares them, leaving out warnings. *)

open Diagnostics.Errors

(* errors.error-type *)
let%expect_test "the error type causes no other error" =
  main "fn f() -> Nope {\n[]\n}";
  [%expect {| main.lt:1: E0211 |}];
  main "fn g(x: Nope) {}\nfn f() {\ng(List.new())\n}";
  [%expect {| main.lt:1: E0211 |}];
  main "fn f() {\nlet x: List<Nope> = []\nlet y = []\n}";
  [%expect {| main.lt:2: E0211 |}];
  main "fn f() {\nlet (a, b) = nope()\nlet n = a.len()\n}";
  [%expect {| main.lt:2: E0211 |}];
  main "fn f() {\nnope(|x| x.len())\n}";
  [%expect {| main.lt:2: E0211 |}];
  main "fn f(xs: List<str>) {\nxs.mapp(|x| x.len())\n}";
  [%expect {| main.lt:2: E0314 |}];
  main "fn f(xs: List<str>) -> i64 {\nxs.len(|y| y.len())\n}";
  [%expect {| main.lt:2: E0315 |}];
  main
    "fn apply(f: fn(i64) -> i64) -> i64 { f(1) }\n\
     fn g() -> i64 {\n\
     apply(|a, b| a.len())\n\
     }";
  [%expect {| main.lt:3: E0315 |}]

(* errors.error-type *)
let%expect_test "an impl with an error still declares its members" =
  main
    "type P<T> = { x: T }\n\
     impl P<i64> { fn get(self) -> i64 { 0 } }\n\
     fn f(p: P<i64>) -> i64 {\n\
     p.get()\n\
     }";
  [%expect {| main.lt:2: E0302 |}];
  main
    "type T = {}\n\
     impl Nope for T { fn name(self) -> str { \"\" } }\n\
     fn f(t: T) -> str {\n\
     t.name()\n\
     }";
  [%expect {| main.lt:2: E0211 |}]

(* errors.root-causes, and numbers.float-literals *)
let%expect_test "an error elsewhere hides no error of its own" =
  main
    "fn takes(s: str) {}\nfn f() {\nlet x = 1.5\ntakes(x, 2)\nlet n: i64 = x\n}";
  [%expect {|
    main.lt:4: E0315
    main.lt:5: E0311
    |}]

(* errors.error-type *)
let%expect_test "a pattern or value that fails its shape causes no other error"
    =
  main
    "fn f() {\n\
     let xs = [(1, 2)]\n\
     let ys = nope(xs, .0)\n\
     let zs = xs.mapp(.0)\n\
     }";
  [%expect {|
    main.lt:3: E0211
    main.lt:4: E0314
    |}];
  main
    "fn a(n: i64) -> i64 {\n\
     let (x, y) = n\n\
     x.abs()\n\
     }\n\
     fn b(n: i64) -> i64 {\n\
     let y = n else return 0\n\
     y.abs()\n\
     }\n\
     fn c(n: i64) -> i64 {\n\
     let Some(x) = n else return 0\n\
     x.abs()\n\
     }\n\
     fn d(n: i64) -> i64 {\n\
     match n {\n\
     [x, ..] => x.abs()\n\
     _ => 0\n\
     }\n\
     }";
  [%expect
    {|
    main.lt:2: E0311
    main.lt:6: E0311
    main.lt:10: E0311
    main.lt:15: E0311
    |}];
  main "fn f() {\nlet g: fn(i64) -> i64 = |x: str| 1\n}";
  [%expect {| main.lt:2: E0311 |}];
  main
    "fn f() {\n\
     let k = |x| {\n\
     let y: i64 = if true { x }\n\
     x + 1\n\
     }\n\
     let n: i64 = k(1)\n\
     }";
  [%expect {| main.lt:3: E0323 |}];
  main
    "fn describe(n: i64) -> str { \"{n}\" }\n\
     fn f() -> str {\n\
     describe(inout 5)\n\
     }";
  [%expect {| main.lt:3: E0400 |}];
  main
    "type Box<T> = { x: T }\n\
     impl Box<Nope> { fn name(self) -> str { \"box\" } }\n\
     fn f(b: Box<i64>) -> str { b.name() }";
  [%expect {| main.lt:2: E0211 |}]
