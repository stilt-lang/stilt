(* Tests of the implicit [alloc] effect in phase 2 of checking a body (errors.phases): which operations allocate (facts.allocation), and the checks of
   [without alloc] (facts.without-alloc) and of a function's own clause (declarations.limits). Each test prints a program's diagnostics as conformance.diagnostic-lines compares
   them, warnings included. *)

open Diagnostics

(* facts.allocation and facts.without-alloc *)
let%expect_test "a module without alloc has no operation that allocates" =
  main
    "module main\n\
     without alloc\n\
     type Tree = | Leaf | Node(Tree, i64, Tree)\n\
     type Link = { next: Option<Link> }\n\
     type Point = { x: i64, y: i64 }\n\
     fn list() -> List<i64> { [1] }\n\
     fn closure() -> fn() -> i64 { || 1 }\n\
     fn text(n: i64) -> str { \"{n}\" }\n\
     fn node(t: Tree) -> Tree { Node(t, 1, t) }\n\
     fn leaf() -> Tree { Leaf }\n\
     fn ctor() -> fn(Tree, i64, Tree) -> Tree { Node }\n\
     fn link() -> Link { Link { next: None } }\n\
     fn point() -> Point { Point { x: 1, y: 2 } }\n\
     fn store(inout xs: List<i64>) { xs[0] = 1 }\n\
     fn bump(inout m: Map<str, i64>) { m[\"a\"] += 1 }\n\
     fn swap(inout a: i64, inout b: i64) {}\n\
     fn pass(inout xs: List<i64>, inout y: i64) { swap(inout xs[0], inout y) }\n\
     fn push(inout xs: List<i64>) { xs.push(1) }\n\
     fn read(xs: List<i64>) -> i64 { xs[0] }\n\
     fn get(xs: List<i64>) -> Option<i64> { xs.get(0) }\n\
     fn plain() -> str { \"plain\" }\n\
     fn shown(n: i64) -> str { n.show() }\n\
     fn apply(f: fn() -> i64) -> i64 { f() }\n\
     test \"tests may allocate\" { assert [1] == [1] }";
  (* The interpolation allocates, and so does the built-in [show] of its
     splice, one error for their line (facts.without). [store] writes its [inout] parameter in place, since the module's
     limit makes it hold its own storage (facts.own-storage and facts.writes-in-place). *)
  [%expect
    {|
    main.lt:6: E0204
    main.lt:7: E0204
    main.lt:8: E0204
    main.lt:9: E0204
    main.lt:11: E0204
    main.lt:12: E0204
    main.lt:15: E0204
    main.lt:17: E0204
    main.lt:18: E0204
    main.lt:22: E0204
    |}]

(* facts.inference, facts.calls-through-function-values and facts.without-alloc *)
let%expect_test
    "allocations are inherited, and calls of function values add none" =
  check
    [
      ("main.lt", "use lib\nuse pure\nfn main() {}\n");
      ( "lib.lt",
        "module lib\n\
         pub fn build() -> List<i64> { [1] }\n\
         pub fn via() -> i64 { build().len() }\n\
         pub fn sum(xs: List<i64>) -> i64 { xs.fold(0, |a, x| a + x) }\n\
         pub fn len(xs: List<i64>) -> i64 { xs.len() }\n\
         pub fn maker() -> fn() -> i64 { || 1 }" );
      ( "pure.lt",
        "module pure\n\
         without alloc\n\
         use lib\n\
         pub fn a() -> i64 { lib.via() }\n\
         pub fn b(xs: List<i64>) -> i64 { lib.len(xs) }\n\
         pub fn c(f: fn() -> i64) -> i64 { f() }\n\
         pub fn d() -> fn() -> i64 { lib.maker() }\n\
         pub fn e(xs: List<i64>) -> i64 { xs.fold(0, |a, x| a + x) }\n\
         pub fn g(xs: List<i64>) -> i64 { lib.sum(xs) }" );
    ];
  [%expect
    {|
    pure.lt:4: E0204
    pure.lt:7: E0204
    pure.lt:8: E0204
    pure.lt:9: E0204
    |}]

(* declarations.limits; effects.without-panic; facts.without-alloc *)
let%expect_test "a function's clause limits its own body" =
  (* A limited function counts as one without the fact, wherever it is
     named, so [uses] and [wraps] get no error. *)
  main
    "fn at(xs: List<i64>) -> i64 without panic { xs[0] }\n\
     fn uses(xs: List<i64>) -> i64 without panic { at(xs) }\n\
     fn first(xs: List<i64>) -> i64 { xs[0] }\n\
     fn calls(xs: List<i64>) -> i64 without panic { first(xs) }\n\
     fn apply(f: fn(i64) -> i64) -> i64 without panic, alloc { f(1) }\n\
     fn make() -> List<i64> without alloc { [] }\n\
     fn both(xs: List<i64>) -> List<i64> without panic, alloc { [xs[0]] }\n\
     fn todo() -> i64 without panic = ?\n\
     fn caller() -> List<i64> without panic { make() }\n\
     fn wraps() -> List<i64> without alloc { make() }";
  [%expect
    {|
    main.lt:1: E0204
    main.lt:4: E0204
    main.lt:6: E0204
    main.lt:7: E0204
    main.lt:7: E0204
    main.lt:8: E0204
    |}]

(* declarations.limits *)
let%expect_test "methods take clauses of their own" =
  main
    "type Box = { n: i64 }\n\
     impl Box {\n\
     fn get(self) -> i64 without alloc { self.n }\n\
     fn list(self) -> List<i64> without alloc { [self.n] }\n\
     }\n\
     trait T {\n\
     fn t(self) -> i64 without panic { 1 / 0 }\n\
     }";
  [%expect {|
    main.lt:4: E0204
    main.lt:7: E0204
    |}]

(* effects.without-overflow *)
let%expect_test "a limit that a module and its function both set counts once" =
  main
    "module main\n\
     without panic\n\
     fn at(xs: List<i64>) -> i64 without panic, alloc { xs[0] }";
  [%expect {| main.lt:3: E0204 |}]
