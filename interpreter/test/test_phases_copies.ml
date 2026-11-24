(* Tests of the warning for duplicate bodies (docs.bodies-compared, docs.body-size, docs.same-body and docs.duplicate-bodies). Each test
   prints a program's diagnostics as conformance.diagnostic-lines compares them, warnings
   included. *)

open Diagnostics

let sum = "a * b + a * 2 + b * 3 - a - b - 9 * 1"

(* docs.body-size, docs.same-body and docs.duplicate-bodies *)
let%expect_test "each later copy is warned, naming the first" =
  main
    (String.concat "\n"
       [
         "fn one(a: i64, b: i64) -> i64 { " ^ sum ^ " }";
         "fn two(x: i64, y: i64) -> i64 { "
         ^ "x * y + x * 2 + y * 3 - x - y - 9 * 1 }";
         "fn small(a: i64) -> i64 { a * 2 + a }";
         "fn small_again(a: i64) -> i64 { a * 2 + a }";
         "fn narrow(a: i32, b: i32) -> i32 { " ^ sum ^ " }";
         "fn three(a: i64, b: i64) -> i64 { " ^ sum ^ " }";
       ]);
  [%expect {|
    main.lt:2: W0302
    main.lt:6: W0302 |}]

(* docs.same-body and docs.duplicate-bodies: the file whose path sorts last holds the copy, and
   one text that calls different functions isn't one. *)
let%expect_test "copies across modules" =
  let body = "{ helper(x) * 2 + helper(x + 1) * 3 - helper(x * 2) }" in
  let shared = "{ c.base(x) * 2 + c.base(x + 1) * 3 - c.base(x * 2) }" in
  let module_ helper =
    "use c\nfn helper(x: i64) -> i64 { " ^ helper
    ^ " }\npub fn scaled(x: i64) -> i64 " ^ body
    ^ "\npub fn shared(x: i64) -> i64 " ^ shared
  in
  check
    [
      ("main.lt", "fn main() {}");
      ("b.lt", module_ "x - 1");
      ("a.lt", module_ "x + 1");
      ("c.lt", "pub fn base(x: i64) -> i64 { x * x }");
    ];
  [%expect {| b.lt:4: W0302 |}]

(* docs.body-size, and errors.parts: the parts after a lexical error are
   read, and their bodies' tokens counted, as any others. *)
let%expect_test "the bodies after a lexical error are compared" =
  let body = "{ a * 2 + b * 3 + a * b + a * a * b - 1 }" in
  main
    (String.concat "\n"
       [
         "type Order = { qty: i64, extra: i64\"{{\" }";
         "fn mass(a: i64, b: i64) -> i64 " ^ body;
         "fn heft(a: i64, b: i64) -> i64 " ^ body;
       ]);
  [%expect {|
    main.lt:1: E0006
    main.lt:3: W0302 |}]

(* docs.bodies-compared *)
let%expect_test "a body with an error isn't compared" =
  let body = "{ a / b + a * 2 + b * 3 + a * b - 1 * 1 }" in
  main
    ("fn limited(a: i64, b: i64) -> i64 without panic " ^ body
   ^ "\nfn free(a: i64, b: i64) -> i64 " ^ body);
  [%expect {| main.lt:1: E0204 |}]
