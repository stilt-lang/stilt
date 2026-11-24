(* Tests of the parser against the production of reference/03-syntax.md that meta.bound-tests
   adds: the bound test, the whole condition of an [if] or an [else if],
   printed as the grammar's table gives it. *)

open Stilt

let show text =
  match Syntax.parse ~file:"t.lt" text with
  | Ok (m, _) -> print_endline (Sexp.of_module m)
  | Error diagnostic -> print_endline (Diagnostic.to_string diagnostic)

(* meta.bound-tests *)
let%expect_test "a bound test and its else if" =
  show "fn f<T>() { if T: Show + From<List<i64>> { 1 } else if T: Eq { 2 } }";
  [%expect
    {| (module (fn f (T) () (tuple) (row) (block (if (bound T Show (From (List i64))) (block 1) (if (bound T Eq) (block 2)))))) |}];
  show "fn f<T>() { comptime if T: Show {} else {} }";
  [%expect
    {| (module (fn f (T) () (tuple) (row) (block (comptime (if (bound T Show) (block) (block)))))) |}]

(* A bound test is the whole condition: inside another expression, its [:]
   is a syntax error. *)
let%expect_test "a bound test stands only as a whole condition" =
  show "fn f<T>(a: bool) { if a && T: Show {} }";
  [%expect {| t.lt:1:29: E0100: unexpected `:` |}];
  show "fn f<T>() { let b = T: Show }";
  [%expect {| t.lt:1:22: E0100: unexpected `:` |}]
