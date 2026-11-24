open Model_json
open Model_types
open Model_ops
open Model_forms

(* Views that write in the Lean model's calculus, as the reference interpreter holds them: a
   writable binding holds a copy of the part it writes, and the end of its scope writes the
   copy back into its source (projections.writable-views and projections.what-view-writes).
   While the binding lives, nothing else reaches the source (projections.reaching-written-source),
   so no run tells the copy from a window. *)

type callbacks = {
  expr : Tast.expr -> Model_json.t;
  block : Tast.block -> Model_json.t;
}

let owns (i : Hir.item) =
  i.home = "std.view" && List.mem i.name [ "into"; "part"; "split" ]

let i64 = prelude_ty "i64"
let list_op name operands = op (tag "list" [ Str name ]) operands
let add a b = op (tag "arith" [ Str "add"; Str "i64" ]) [ a; b ]
let int n = tag "int" [ Str (string_of_int n) ]

let bound lets body =
  List.fold_right
    (fun (n, t, init) b -> tag "letIn" [ Str n; t; init; b ])
    lets body

(* The source of a view made through [inout]: its type, a list's, its index expressions'
   temporaries, how a value is stored into it, and the expression that reads it. *)
let source cb cx (src : Tast.expr) =
  let t = match Model_views.viewed src.ty with Some t -> t | None -> src.ty in
  let lets, store, read = Model_places.receiver ~expr:cb.expr cx src in
  (t, lets, store, read)

(* Each part, a variable and its offset, written back into the source, which is then
   stored. *)
let written_back cx loc t store read parts =
  let w = temp "written" loc in
  let copy (p, at) rest =
    let j = temp "element" loc in
    let range = tag "list" [ tag "range" [ Bool false ] ] in
    let each = op range [ int 0; list_op "len" [ var_e p ] ] in
    let target = Arr [ Str w; Arr [ tag "index" [ add at (var_e j) ] ] ] in
    let put = tag "assign" [ target; tag "index" [ var_e p; var_e j ] ] in
    tag "seq" [ tag "for" [ Str j; ty cx i64; each; put ]; rest ]
  in
  tag "varIn"
    [
      Str w;
      ty cx t;
      read;
      List.fold_right copy parts (Model_places.write store (var_e w));
    ]

(* The error types that code may raise, outside its closure literals: those of its
   [raise]s and of the rows of its calls. *)
let rec raised (e : Tast.expr) =
  let row (r : Types.row) = Option.to_list (Types.row_contents r).raise in
  let own =
    match e.desc with
    | Raise x -> [ x.ty ]
    | Call (_, _, _, r) -> row r
    | Call_value (f, _) -> (
        match norm f.ty with Fn (_, _, r) -> row r | _ -> [])
    | _ -> []
  in
  match e.desc with
  | Closure _ | Handler _ -> []
  | _ -> own @ List.concat_map raised (Walk.children e)

(* The one error type that code may raise, if any. *)
let raise_of cx (es : Tast.expr list) =
  match List.concat_map raised es with
  | [] -> None
  | t :: ts ->
      let key t = Model_json.to_string (ty cx t) in
      if List.for_all (fun u -> key u = key t) ts then Some t
      else outside "a writable view's scope that raises errors of two types"

(* [body], of type [rt], then [back], which a raise of [err] in [body] runs before it
   leaves. *)
let around cx loc rt err body back =
  let r = temp "scope" loc in
  let ended =
    tag "letIn" [ Str r; ty cx rt; body; tag "seq" [ back; var_e r ] ]
  in
  match err with
  | None -> ended
  | Some err ->
      let x = temp "raised" loc in
      let again = tag "seq" [ back; tag "raise" [ var_e x ] ] in
      tag "tryCatch" [ ended; ty cx err; Str x; again; ty cx rt ]

(* Whether code jumps out of a block: a [return], or a [break] or a [continue] of a loop
   outside it. *)
let rec jumps_out ~in_loop (e : Tast.expr) =
  match e.desc with
  | Return _ -> true
  | Break | Continue -> not in_loop
  | Closure _ | Handler _ -> false
  | Loop _ | While _ | For _ ->
      List.exists (jumps_out ~in_loop:true) (Walk.children e)
  | _ -> List.exists (jumps_out ~in_loop) (Walk.children e)

let no_jumps (b : Tast.block) =
  if List.exists (jumps_out ~in_loop:false) (Walk.block_exprs b) then
    outside "a jump out of a writable view's scope"

(* [var v = view.into(inout src, a, b)] or [view.part(inout src, a, b)], and the rest of
   its block: the part copied into [v], which the rest writes, and written back into
   [src] when the rest ends or raises (projections.writable-bindings). *)
let binding cb cx (v : Hir.var) (init : Tast.expr) (rest : Tast.block) =
  match init.desc with
  | Call (Function i, _, [ { mode = Inout; value = src }; a; b ], _)
    when owns i && i.name <> "split" ->
      no_jumps rest;
      let t, lets, store, read = source cb cx src in
      let start = temp "start" a.value.loc and stop = temp "end" b.value.loc in
      let lets =
        lets
        @ [
            (start, ty cx i64, cb.expr a.value);
            (stop, ty cx i64, cb.expr b.value);
          ]
      in
      cx.writable <- v.id :: cx.writable;
      let name = var_name v in
      let part = list_op "slice" [ read; var_e start; var_e stop ] in
      let back =
        written_back cx init.loc t store read [ (name, var_e start) ]
      in
      let err = raise_of cx (Walk.block_exprs rest) in
      let scope = around cx init.loc (block_ty rest) err (cb.block rest) back in
      bound lets (tag "varIn" [ Str name; ty cx t; part; scope ])
  | _ -> outside "a writable view that view.into or view.part doesn't make"

let fresh = ref (-500000)

let local name (t : Types.ty) (loc : Ast.loc) =
  decr fresh;
  let v = { Hir.id = !fresh; name; loc } in
  (v, { Tast.desc = Local v; ty = t; loc })

(* [view.split(inout src, at, f)]: the parts before and from [at] copied into two
   variables, which [f] takes [inout], and written back when it returns or raises. *)
let split cb cx (e : Tast.expr) (src : Tast.expr) (at : Tast.expr)
    (f : Tast.expr) =
  let t, lets, store, read = source cb cx src in
  let at_n = temp "at" at.loc in
  let fv, fl = local "split-f" f.ty f.loc in
  let lets =
    lets
    @ [ (at_n, ty cx i64, cb.expr at); (var_name fv, ty cx f.ty, cb.expr f) ]
  in
  let view = Types.Con (Model_views.view_item, [ t ]) in
  let lv, ll = local "before" view e.loc and rv, rl = local "from" view e.loc in
  let args = List.map (fun value -> { Tast.mode = Inout; value }) [ ll; rl ] in
  let call_e = { e with desc = Call_value (fl, args) } in
  let call = cb.expr call_e in
  let err = raise_of cx [ call_e ] in
  let l = var_name lv and r = var_name rv in
  let back =
    written_back cx e.loc t store read [ (l, int 0); (r, var_e at_n) ]
  in
  let after = list_op "slice" [ read; var_e at_n; list_op "len" [ read ] ] in
  bound lets
    (tag "varIn"
       [
         Str l;
         ty cx t;
         list_op "slice" [ read; int 0; var_e at_n ];
         tag "varIn"
           [
             Str r;
             ty cx t;
             after;
             around cx e.loc (Types.Tuple []) err call back;
           ];
       ])

(* A call of [view.into] or [view.part] that no writable binding holds, which reads
   (projections.what-view-writes): a view of the part, as [View.of] gives, of the source
   read when the call starts, after the offsets (values.inout-argument-order); and
   [view.split]. *)
let call cb cx (e : Tast.expr) (i : Hir.item) (args : Tast.arg list) =
  match (i.name, args) with
  | ("into" | "part"), [ src; a; b ] ->
      let _, lets, _, read = source cb cx src.value in
      let start = temp "start" a.value.loc and stop = temp "end" b.value.loc in
      bound
        (lets
        @ [
            (start, ty cx i64, cb.expr a.value);
            (stop, ty cx i64, cb.expr b.value);
          ])
        (Model_views.view [ read; var_e start; var_e stop ])
  | "split", [ src; at; f ] -> split cb cx e src.value at.value f.value
  | _ -> outside "the function std.view.%s" i.name
