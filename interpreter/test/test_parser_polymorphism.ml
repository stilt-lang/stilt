(* Tests of the parser against the production of reference/03-syntax.md that polymorphism.function-types
   extends: a function type that declares type parameters, printed as the
   grammar's table gives it. *)

open Stilt

let show text =
  match Syntax.parse ~file:"t.lt" text with
  | Ok (m, _) -> print_endline (Sexp.of_module m)
  | Error diagnostic -> print_endline (Diagnostic.to_string diagnostic)

(* polymorphism.function-types *)
let%expect_test "a polymorphic function type lists its generics first" =
  show "fn f(g: fn<T: Show, U>(T, U) -> str / io) {}";
  [%expect
    {| (module (fn f () ((g (fn ((T Show) U) (T U) str (row io)))) (tuple) (row) (block))) |}];
  show "fn f(g: fn(i64) -> i64) {}";
  [%expect
    {| (module (fn f () ((g (fn (i64) i64 (row)))) (tuple) (row) (block))) |}]

(* A [>>] closes a bound's arguments and the generics at once, and a list of
   type arguments and a function type's result. *)
let%expect_test "a polymorphic function type and [>>]" =
  show "fn f(g: fn<C: Collection<i64>>(C) -> i64) {}";
  [%expect
    {| (module (fn f () ((g (fn ((C (Collection i64))) (C) i64 (row)))) (tuple) (row) (block))) |}];
  show "type T = { f: Option<fn<A>(A) -> List<A>> }";
  [%expect
    {| (module (type T () (record (f (Option (fn (A) (A) (List A) (row))))))) |}]

(* The grammar's note on polymorphic function types: no row variables. *)
let%expect_test "a polymorphic function type declares no row variable" =
  show "fn f(g: fn<e>() -> i64) {}";
  [%expect {| t.lt:1:12: E0100: unexpected `e` |}]
