(* A call with an [inout] argument through a map's element, [f(inout m[k])], which the
   calculus has no place for: its value is read into a fresh variable, which the call
   takes [inout], and stored back with [m[k] = v] (std.finding-keys). *)

open Model_json
open Model_types
open Model_forms

type callbacks = {
  expr : Tast.expr -> Model_json.t;
  place : Tast.expr -> Model_json.t;
  store : Tast.expr -> Tast.expr -> Model_json.t;
      (** [p = v], a map's element included. *)
}

(* The map's element that a place goes through, [m[k]] with [m] reached without one, and
   the place rebuilt on another root in its stead: [m[k].f] on [t] is [t.f]. *)
let rec map_root (p : Tast.expr) =
  let under b rebuild =
    Option.map
      (fun (e0, m, k, up) -> (e0, m, k, fun t -> rebuild (up t)))
      (map_root b)
  in
  match p.desc with
  | Index (m, k) when is_map m.ty -> Some (p, m, k, fun t -> t)
  | Field (b, f) -> under b (fun b -> { p with desc = Field (b, f) })
  | Tuple_field (b, i) ->
      under b (fun b -> { p with desc = Tuple_field (b, i) })
  | Index (b, i) -> under b (fun b -> { p with desc = Index (b, i) })
  | _ -> None

(* Whether reading a place can panic: whether it indexes something. *)
let rec indexes (p : Tast.expr) =
  match p.desc with
  | Index _ -> true
  | Field (b, _) | Tuple_field (b, _) -> indexes b
  | _ -> false

let local (e : Tast.expr) name id ty : Tast.expr =
  { e with desc = Local { Hir.id; name; loc = e.loc }; ty }

(* What an argument becomes: the bindings made in its turn, the read made when the call
   starts, the argument passed, and the store made when it ends. *)
type part = {
  binds : (string * Types.ty * Model_json.t) list;
  read : (string * Types.ty * Model_json.t) option;
  passed : Model_json.t;
  back : Model_json.t option;
}

let part cb cx (e : Tast.expr) j (a : Tast.arg) =
  let name what = Printf.sprintf "%s/%d" (temp what e.loc) j in
  match (a.mode, map_root a.value) with
  | Inout, Some ((e0 : Tast.expr), m, k, rebuild) ->
      if map_root m <> None then outside "a place through two maps' elements";
      let key = local e (name "inout-key") ((-2 * j) - 100) k.ty in
      let entry = { e0 with desc = Index (m, key) } in
      let t = local e (name "inout-entry") ((-2 * j) - 101) e0.ty in
      let var_of (x : Tast.expr) =
        match x.desc with Local v -> var_name v | _ -> ""
      in
      {
        binds = [ (var_of key, k.ty, cb.expr k) ];
        read = Some (var_of t, e0.ty, cb.expr entry);
        passed = tag "inout" [ cb.place (rebuild t) ];
        back = Some (cb.store entry t);
      }
  | Inout, None ->
      if indexes a.value then
        outside "an inout argument beside one through a map";
      {
        binds = [];
        read = None;
        passed = tag "inout" [ cb.place a.value ];
        back = None;
      }
  | Let, _ ->
      let v = name "argument" in
      {
        binds = [ (v, a.value.ty, cb.expr a.value) ];
        read = None;
        passed = tag "value" [ var_e v ];
        back = None;
      }

let lets bindings body =
  List.fold_right
    (fun (n, t, v) acc -> tag "letIn" [ Str n; t; v; acc ])
    bindings body

(* The call [e], made by [make] of the arguments passed: the arguments in turn, then the
   places read, left to right, then the call, then each store, left to right, when the
   call returns and when it raises the error [raise] (values.inout-argument-order). *)
let through_maps cb cx (e : Tast.expr) ~raise make (args : Tast.arg list) =
  let parts = List.mapi (part cb cx e) args in
  let typed (n, t, v) = (n, ty cx t, v) in
  let binds = List.concat_map (fun p -> List.map typed p.binds) parts in
  let reads = List.filter_map (fun p -> Option.map typed p.read) parts in
  let backs = List.filter_map (fun p -> p.back) parts in
  let stored x = List.fold_right (fun b acc -> tag "seq" [ b; acc ]) backs x in
  let call = make (List.map (fun p -> p.passed) parts) in
  let call =
    match raise with
    | None -> call
    | Some err ->
        let error = temp "inout-error" e.loc in
        let again = tag "raise" [ var_e error ] in
        tag "tryCatch" [ call; ty cx err; Str error; stored again; ty cx e.ty ]
  in
  let result = temp "inout-result" e.loc in
  lets binds
    (lets reads
       (tag "letIn" [ Str result; ty cx e.ty; call; stored (var_e result) ]))

(* Whether a call has an [inout] argument through a map's element. *)
let has_map_inout (args : Tast.arg list) =
  List.exists
    (fun (a : Tast.arg) -> a.mode = Inout && map_root a.value <> None)
    args
