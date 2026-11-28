(* Iterators in the Lean model's calculus (formal/Stilt/Typing/Iters.lean): an [Iter<T>] is a
   record of the library whose one field asks for the next element and the iterator of the
   rest, and each function of [impl<T> Iter<T>] is a form of the calculus, the call of the
   function the model declares for it, which the export declares once by its name
   (views.making-iterator, views.adapters and views.consumers). *)

open Model_json
open Model_types
open Model_forms

let iter_item = { Hir.home = "std.view"; name = "Iter" }

let element t =
  match norm t with
  | Types.Con (i, [ e ]) when i = iter_item -> Some e
  | _ -> None

let elem_of t =
  match element t with
  | Some e -> e
  | None -> outside "an iterator of a type the model lacks"

(* The form that calls the function [name] the model declares, at the type arguments [ts] and
   the rows [rows], declared once by its name, on the values [args], of the result type [r]. *)
let form cx name ts rows args r =
  let key = "std.view.Iter." ^ name in
  if not (List.mem_assoc key cx.helpers) then
    cx.helpers <- (key, Str key) :: cx.helpers;
  tag "iter"
    [
      Str key;
      Arr (List.map (ty cx) ts);
      Arr rows;
      Arr (List.map (fun a -> tag "value" [ a ]) args);
      ty cx r;
    ]

let int n = tag "int" [ Str n ]

(* The row of a consumer's callback, which its implicit row variable takes. *)
let callback_row cx (f : Tast.expr) =
  match norm f.ty with
  | Types.Fn (_, _, rw) -> row cx rw
  | _ -> outside "a callback of a type the model lacks"

(* [|a, b| a < b] at [t], [<] as [Ord] orders [t]: the comparison [max] and [min] take. *)
let less ~expr cx (loc : Ast.loc) t =
  let var name id = { Hir.id; name; loc } in
  let a = var "a" (-1) and b = var "b" (-2) in
  let local v = { Tast.desc = Local v; ty = t; loc } in
  let lt =
    { Tast.desc = Binary (Lt, local a, local b); ty = prelude_ty "bool"; loc }
  in
  let param v = Arr [ Str "let"; Str (var_name v); ty cx t; Null ] in
  tag "closure"
    [
      Arr [ param a; param b ];
      Str "bool";
      Arr [ Bool false; Null; Arr [] ];
      expr lt;
    ]

(* A call [e] of a function of [impl<T> Iter<T>] on the arguments [args]: [Iter.of],
   [Iter.of_view], whose iterator iterates the view's part, the adapters and the consumers. *)
let call ~expr cx (e : Tast.expr) name (args : Tast.arg list) =
  let values = List.map (fun (a : Tast.arg) -> expr a.value) args in
  let self () =
    match args with
    | a :: _ -> elem_of a.value.ty
    | [] -> outside "a function of an iterator"
  in
  let row_of i = callback_row cx (List.nth args i).value in
  match (name, values) with
  | "of", [ xs ] -> form cx "of" [ elem_of e.ty ] [] [ xs; int "0" ] e.ty
  | "of_view", [ v ] ->
      form cx "of"
        [ elem_of e.ty ]
        []
        [ Model_ops.op (Str "copy") [ v ]; int "0" ]
        e.ty
  | "map", [ _; _ ] -> form cx name [ self (); elem_of e.ty ] [] values e.ty
  | "zip", [ _; _ ] ->
      let other = elem_of (List.nth args 1).value.ty in
      form cx name [ self (); other ] [] values e.ty
  | ( ( "filter" | "take" | "skip" | "enumerate" | "chain" | "take_while"
      | "skip_while" ),
      [ _; _ ] ) ->
      form cx name [ self () ] [] values e.ty
  | ("collect" | "count" | "first" | "last"), [ _ ] ->
      form cx name [ self () ] [] values e.ty
  | "nth", [ _; _ ] -> form cx name [ self () ] [] values e.ty
  | "fold", [ _; _; _ ] ->
      form cx name [ self (); e.ty ] [ row_of 2 ] values e.ty
  | ("any" | "all" | "find"), [ _; _ ] ->
      form cx name [ self () ] [ row_of 1 ] values e.ty
  | ("max" | "min"), [ it ] ->
      form cx name [ self () ] [] [ it; less ~expr cx e.loc (self ()) ] e.ty
  | _ -> outside "the function std.view.Iter.%s" name

(* [view.range(start, end)], [view.of_map(m)], whose iterator iterates the map's entries in
   insertion order (views.making-iterator), and [view.chars(v)] and [view.bytes(v)]. *)
let view_call cx (e : Tast.expr) name (args : Tast.arg list) values =
  match (name, args, values) with
  | "range", _, [ a; b ] -> form cx "range" [] [] [ a; b ] e.ty
  | "of_map", [ m ], [ v ] -> (
      match norm m.value.ty with
      | Types.Con (_, [ k; _ ]) when key cx k ->
          form cx "of"
            [ elem_of e.ty ]
            []
            [ map_op "entries" [ v ]; int "0" ]
            e.ty
      | _ ->
          outside "an iterator of a map whose keys the model compares otherwise"
      )
  | ("chars" | "bytes"), _, [ v ] ->
      (* views.functions-of-views: the sequences that [chars] and [bytes] of [str] build, of
         the view's part. *)
      let part =
        Model_ops.op (tag "list" [ Str name ])
          [ Model_ops.op (Str "copy") [ v ] ]
      in
      form cx "of" [ elem_of e.ty ] [] [ part; int "0" ] e.ty
  | _ -> outside "the function std.view.%s" name

(* views.for-over-view: [for x in it { body }], the iterator bound to [c] and asked for one
   element at a time, the rest kept in [c] before [body] runs, so that a [continue] goes on with
   the next element, until it ends. *)
let loop cx (loc : Ast.loc) t it x body =
  let c = temp "for-iterator" loc and r = temp "for-rest" loc in
  let iter = Types.Con (iter_item, [ t ]) in
  let step = Types.Con (option_item, [ Types.Tuple [ t; iter ] ]) in
  let ask = call_e cx (tag "field" [ var_e c; Str "next" ]) [] step in
  let opt = "std.prelude.Option" in
  let bind n = tag "bind" [ Str n ] in
  let pair = tag "tuple" [ Arr [ bind x; bind r ] ] in
  let some = tag "variant" [ Str opt; Str "Some"; Arr [ pair ] ] in
  let none = tag "variant" [ Str opt; Str "None"; Arr [] ] in
  let next = tag "assign" [ Arr [ Str c; Arr [] ]; var_e r ] in
  let arms =
    [
      Arr [ some; Arr [ Str x; Str r ]; tag "seq" [ next; body ] ];
      Arr [ none; Arr []; Str "break" ];
    ]
  in
  tag "varIn"
    [
      Str c;
      ty cx iter;
      it;
      tag "loop" [ tag "match" [ ask; Str "unit"; Arr arms ] ];
    ]
