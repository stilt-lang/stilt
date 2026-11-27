(* Views in the Lean model's calculus, as the reference interpreter holds them: a view is
   the part it reads, a [str] or a list, which the calculus's view gives a view type and
   [copy] gives back its own (views.what-view-is). Every other function of a view reads its part,
   so it is written as the same function of the part's type on the view's [copy]
   (views.functions-of-views). *)

open Model_json
open Model_types
open Model_ops

let view_item = { Hir.home = "std.view"; name = "View" }

let viewed t =
  match norm t with
  | Types.Con (i, [ v ]) when i = view_item -> Some v
  | _ -> None

let is_list t =
  match norm t with
  | Types.Con ({ home = "std.prelude"; name = "List" }, [ _ ]) -> true
  | _ -> false

(* [x.copy()] when [x] is a view: the viewed part, of the viewed type. *)
let copied (x : Tast.expr) =
  match viewed x.ty with
  | Some t ->
      let arg = { Tast.mode = Ast.Let; value = x } in
      {
        x with
        desc = Call (Member (view_item, "copy"), [], [ arg ], Types.empty_row);
        ty = t;
      }
  | None -> x

(* An expression whose operands are views, read through their parts: [v[i]], a [for]
   over [v], a splice of [v] and an operator on views, each of which reads the viewed
   part as the same form of the part's type does (views.functions-of-views,
   views.for-over-view). *)
let desugar (e : Tast.expr) =
  let splice = function
    | Tast.Splice (x, spec) -> Tast.Splice (copied x, spec)
    | s -> s
  in
  match e.desc with
  | Index (b, i) when viewed b.ty <> None ->
      { e with desc = Index (copied b, i) }
  | For (p, Iter it, b) when viewed it.ty <> None ->
      { e with desc = For (p, Iter (copied it), b) }
  | Interpolated segs -> { e with desc = Interpolated (List.map splice segs) }
  | Binary (b, x, y) when viewed x.ty <> None ->
      { e with desc = Binary (b, copied x, copied y) }
  | _ -> e

(* A function of a view, of the part's type [t]: [len] and [is_empty] of a [str] or a
   list. *)
let of_part t name operands =
  if is_list t then op (tag "list" [ Str name ]) operands
  else op (Str name) operands

(* A view of its operands, the source first: the calculus's form of [View.of], [View.all]
   and [v.view] (views.making-view). *)
let view operands = tag "view" [ Arr operands ]

(* A call [e] of a function of [impl<T> View<T>]: [View.of(source, start, end)],
   [View.all(source)] and [v.view(start, end)], the calculus's view, [len], [is_empty]
   and [copy] (views.functions-of-views). *)
let call ~expr (e : Tast.expr) name (args : Tast.arg list) =
  let values = List.map (fun (a : Tast.arg) -> expr a.value) args in
  let part () =
    match args with
    | a :: _ -> (
        match viewed a.value.ty with
        | Some t -> t
        | None -> outside "a function of a view")
    | [] -> outside "a function of a view"
  in
  let copy v = op (Str "copy") [ v ] in
  match (name, values, viewed e.ty) with
  | "of", [ s; a; b ], Some _ -> view [ s; a; b ]
  | "all", [ s ], Some _ -> view [ s ]
  | "view", [ v; a; b ], _ -> view [ v; a; b ]
  | "len", [ v ], _ -> of_part (part ()) "len" [ copy v ]
  | "is_empty", [ v ], _ -> of_part (part ()) "isEmpty" [ copy v ]
  | "copy", [ v ], _ -> copy v
  | _ -> outside "the function std.view.View.%s" name
