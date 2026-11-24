(* Tests of the parser against the productions of reference/03-syntax.md that traits.trait-parameters
   adds: trait parameters, bounds with arguments, [where] clauses, written
   receivers and trait constants, each printed as the grammar's table gives
   it. *)

open Stilt

let show text =
  match Syntax.parse ~file:"t.lt" text with
  | Ok (m, _) -> print_endline (Sexp.of_module m)
  | Error diagnostic -> print_endline (Diagnostic.to_string diagnostic)

(* traits.trait-parameters and traits.trait-constants *)
let%expect_test "a trait's parameters and constants" =
  show "trait Collection<Item> {\nfn at(self, i: i64) -> Option<Item>\n}";
  [%expect
    {| (module (trait Collection (params Item) (fn at () (self (i i64)) (Option Item) (row)))) |}];
  show
    "trait Empty {\nfn empty() -> Self\nconst ZERO: Self\nconst ONE: i64 = 1\n}";
  [%expect
    {| (module (trait Empty (fn empty () () Self (row)) (const ZERO Self) (const ONE i64 1))) |}];
  show "impl Empty for i64 {\nconst ZERO: i64 = 0\n}";
  [%expect {| (module (impl-trait () Empty i64 (const ZERO i64 0))) |}]

(* traits.trait-arguments and traits.bound-arguments: a [>>] closes a bound's arguments and the list of
   generics at once. *)
let%expect_test "bounds and impls with arguments" =
  show "fn f<C: Collection<i64>>(c: C) {}";
  [%expect
    {| (module (fn f ((C (Collection i64))) ((c C)) (tuple) (row) (block))) |}];
  show "fn f<T, C: Show + Collection<List<T>>>(c: C) {}";
  [%expect
    {| (module (fn f (T (C Show (Collection (List T)))) ((c C)) (tuple) (row) (block))) |}];
  show "impl<T> Collection<T> for List<T> {}";
  [%expect {| (module (impl-trait (T) (Collection T) (List T))) |}];
  show "impl<C: Collection<i64>> Show for Shelf<C> {}";
  [%expect {| (module (impl-trait ((C (Collection i64))) Show (Shelf C))) |}]

(* traits.where, and lexical.reserved-words *)
let%expect_test "where clauses" =
  show
    "fn f<C: Collection>(c: C) -> C.Item where C.Item: Ord + Show, D.Key: Hash \
     without panic {}";
  [%expect
    {| (module (fn f ((C Collection)) ((c C)) C.Item (row) (where (C.Item Ord Show) (D.Key Hash)) (without panic) (block))) |}];
  show "impl<C: Collection> Show for Shelf<C> where C.Item: Show {}";
  [%expect
    {| (module (impl-trait ((C Collection)) Show (Shelf C) (where (C.Item Show)))) |}];
  show "fn where() {}";
  [%expect {| t.lt:1:4: E0100: unexpected `where` |}]

(* traits.receiver-types *)
let%expect_test "a receiver's written type" =
  show
    "trait Mappable {\n\
     fn transform<A, B>(self: Self<A>, f: fn(A) -> B) -> Self<B>\n\
     }";
  [%expect
    {| (module (trait Mappable (fn transform (A B) ((self (Self A)) (f (fn (A) B (row)))) (Self B) (row)))) |}];
  show "impl Mappable for List {\nfn m<A>(inout self: List<A>) {}\n}";
  [%expect
    {| (module (impl-trait () Mappable List (fn m (A) ((inout self (List A))) (tuple) (row) (block)))) |}]
