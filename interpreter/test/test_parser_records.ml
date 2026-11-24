(* Tests of the parser against the productions of reference/03-syntax.md that records.anonymous-types
   and variadics.packs extend: anonymous and open record types, record bounds, record
   literals, updates and patterns, packs and spreads, printed as the grammar's
   table gives them. *)

open Stilt

let show text =
  match Syntax.parse ~file:"t.lt" text with
  | Ok (m, _) -> print_endline (Sexp.of_module m)
  | Error diagnostic -> print_endline (Diagnostic.to_string diagnostic)

(* records.anonymous-types, records.record-bounds and records.open-parameter-types *)
let%expect_test "record types and record bounds" =
  show "fn f(p: { name: str, .. }) -> { x: i64, y: i64 } { p }";
  [%expect
    {| (module (fn f () ((p (record-type (name str) ..))) (record-type (x i64) (y i64)) (row) (block p))) |}];
  show "fn f<P: { age: i64, .. } + Show>(p: P) {}";
  [%expect
    {| (module (fn f ((P (record-type (age i64) ..) Show)) ((p P)) (tuple) (row) (block))) |}]

(* records.anonymous-literals and records.update: a [{] followed by a field name and a [:], or by
   [..], begins a record, and [{ x }] stays a block. *)
let%expect_test "record literals and updates" =
  show "fn f() { let a = { x: 1, y }\nlet b = { ..a, x: 2 }\nlet c = { x } }";
  [%expect
    {| (module (fn f () () (tuple) (row) (block (let a (record-lit (x 1) (y y))) (let b (record-lit (.. a) (x 2))) (let c (block x))))) |}];
  show "fn f(p: P) -> P { P { ..p, age: 1 } }";
  [%expect
    {| (module (fn f () ((p P)) P (row) (block (struct P (.. p) (age 1))))) |}]

(* records.anonymous-patterns *)
let%expect_test "anonymous record patterns" =
  show "fn f(p: P) { let { name, age: a, .. } = p }";
  [%expect
    {| (module (fn f () ((p P)) (tuple) (row) (block (let (record _ (name name) (age a) ..) p)))) |}]

(* variadics.packs, variadics.type-spreads and variadics.spread-expressions *)
let%expect_test "packs and spreads" =
  show "type Row<..Ts> = { cells: (..Ts) }";
  [%expect {| (module (type Row ((.. Ts)) (record (cells (tuple (.. Ts)))))) |}];
  show
    "fn f<..Ts: Show, R>(g: fn(..Ts) -> R, xs: (..List<Ts>, i64)) -> R { \
     g(..(..xs)) }";
  [%expect
    {| (module (fn f ((.. Ts Show) R) ((g (fn ((.. Ts)) R (row))) (xs (tuple (.. (List Ts)) i64))) R (row) (block (call g (.. (tuple (.. xs))))))) |}];
  (* A spread alone makes a tuple, as a trailing comma does. *)
  show "fn f() { let a = (..xs)\nlet b = [..xs, 1] }";
  [%expect
    {| (module (fn f () () (tuple) (row) (block (let a (tuple (.. xs))) (let b (list (.. xs) 1))))) |}]

(* The grammar's notes: packs among a trait's or a function type's parameters
   are errors after parsing, and [{}] is no pattern. *)
let%expect_test "where packs parse" =
  show "trait T<..Ts> {}\nfn f(g: fn<..Ts>((..Ts)) -> i64) {}";
  [%expect
    {| (module (trait T (params (.. Ts))) (fn f () ((g (fn ((.. Ts)) ((tuple (.. Ts))) i64 (row)))) (tuple) (row) (block))) |}];
  show "fn f() { let {} = x }";
  [%expect {| t.lt:1:15: E0100: unexpected `}` |}]
