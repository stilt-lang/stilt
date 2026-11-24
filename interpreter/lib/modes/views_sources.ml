(* The sources of views (views.making-view, views.across-calls and views.fixed): which places a view, or
   a closure that captures one, reads, and which it writes (projections.what-view-writes and projections.places-through-views). *)

open Tast
module P = Modes_places
module V = Views_types

type source = Place of P.place | Written of P.place | Temporary of Ast.loc

type binding = {
  sources : source list;
  closure : Ast.loc option;
  writable : bool;
}

type t = (int, binding) Hashtbl.t

let reads = function Place _ | Temporary _ -> true | Written _ -> false
let union a b = a @ List.filter (fun s -> not (List.mem s a)) b
let unions = List.fold_left union []

(* The variables bound inside an expression: by its patterns, and by the
   parameters of the closures in it. *)
let bound_in (e : expr) =
  let found = ref [] in
  let add p = found := P.pattern_vars p @ !found in
  let stmt (s : stmt) =
    match s.stmt with Let b | Var b -> add b.pattern | _ -> ()
  in
  Walk.iter ~stmt
    (fun (e : expr) ->
      match e.desc with
      | Closure (ps, _, _) -> List.iter add ps
      | If_let (p, _, _, _) | For (p, _, _) -> add p
      | Match (_, arms) -> List.iter (fun (a : arm) -> add a.pattern) arms
      | Try (_, Some c) -> List.iter (fun (a : arm) -> add a.pattern) c.arms
      (* shared.when *)
      | When (names, _) ->
          found := List.map (fun (_, (v : Hir.var)) -> v.id) names @ !found
      | _ -> ())
    e;
  !found

let is_fn ty = match Types.resolve ty with Fn _ -> true | _ -> false

(* The sources of a value, which are none for a value that holds no view. A
   view parameter's sources are its argument's, which the callee knows only
   as the parameter itself (views.across-calls). *)
let rec sources t (e : expr) =
  let all es = unions (List.map (sources t) es) in
  match e.desc with
  | Local v -> (
      match Hashtbl.find_opt t v.id with
      (* projections.places-through-views: a writable binding is a source in its own right,
         as a view parameter is. *)
      | Some b when b.writable -> [ Place { root = v; path = [] } ]
      | Some b -> b.sources
      | None when V.is_view e.ty -> [ Place { root = v; path = [] } ]
      | None -> [])
  | Call (_, _, args, _) | Project (_, _, args, _) -> call t e args
  | Call_value (f, args) -> union (sources t f) (call t e args)
  | Closure (params, _, body) -> captured t (params, body)
  | Construct (_, _, es) | Tuple es | List es -> all es
  | Record (_, _, fields) -> all (List.map snd fields)
  | Update (base, fields) -> all (base :: List.map snd fields)
  | Block b -> block t b
  | If (_, b, alt) | If_let (_, _, b, alt) ->
      union (block t b) (all (Option.to_list alt))
  | Match (_, arms) -> all (List.map (fun (a : arm) -> a.body) arms)
  | Try (x, c) ->
      union (sources t x)
        (all (List.map (fun (a : arm) -> a.body) (Walk.catch_arms c)))
  | Else (a, b) -> union (sources t a) (sources t b)
  | Comptime x -> sources t x
  | _ -> []

and block t b =
  match List.rev b with { stmt = Expr e; _ } :: _ -> sources t e | _ -> []

(* views.across-calls: a call's result views every argument whose type is viewable or a
   view type, the receiver included, and writes every one passed [inout]
   (projections.what-view-writes); one that is a projection's call, or no place, is a
   temporary. A result of a function type holds what the closures given to
   the call hold. *)
and call t (e : expr) args =
  if V.is_view e.ty then unions (List.map (argument t) args)
  else if is_fn e.ty then
    unions (List.map (fun (a : arg) -> sources t a.value) args)
  else []

(* The sources that an argument gives the view that a call returns. *)
and argument t (a : arg) =
  match (a.mode, P.place a.value) with
  | Inout, Some p when V.viewable a.value.ty || V.is_view a.value.ty ->
      [ Written p ]
  | Inout, None -> [ Temporary a.value.loc ]
  | Let, Some p when V.viewable a.value.ty -> [ Place p ]
  | Let, None when V.viewable a.value.ty -> [ Temporary a.value.loc ]
  | _ -> sources t a.value

(* views.fixed: a closure literal has the sources of the views it captures. *)
and captured t (params, body) =
  let inside = List.concat_map P.pattern_vars params @ bound_in body in
  let found = ref [] in
  Walk.iter
    (fun (e : expr) ->
      match e.desc with
      | Local v when not (List.mem v.id inside) ->
          found := union !found (sources t e)
      | _ -> ())
    body;
  !found

(* The closure literal that a value is, or that the binding it reads
   holds. *)
let closure t (e : expr) =
  match e.desc with
  | Closure _ when sources t e <> [] -> Some e.loc
  | Local v -> Option.bind (Hashtbl.find_opt t v.id) (fun b -> b.closure)
  | _ -> None

let carries t (e : expr) = V.is_view e.ty || sources t e <> []

(* Binds the variables of [p] that hold the views of [value]; a [var]
   binding of [View<T>] is writable (projections.writable-bindings). *)
let bind ?(var = false) t (p : pattern) (value : expr) =
  if carries t value then
    let sources = sources t value and closure = closure t value in
    let rec go (p : pattern) =
      match p.pat with
      | P_bind v when V.is_view p.pty || (closure <> None && is_fn p.pty) ->
          let writable = var && V.is_window p.pty in
          Hashtbl.replace t v.id { sources; closure; writable }
      | P_tuple ps | P_variant (_, ps) | P_list (ps, _) | P_or ps ->
          List.iter go ps
      | P_record fields -> List.iter (fun (_, q) -> go q) fields
      | _ -> ()
    in
    go p

(* A view assigned to a whole variable adds its sources to the
   variable's. *)
let assign t (v : Hir.var) (value : expr) =
  match Hashtbl.find_opt t v.id with
  | Some b when carries t value ->
      Hashtbl.replace t v.id
        { b with sources = union b.sources (sources t value) }
  | Some _ | None -> ()

(* Every binding of a body that holds a view, in source order: each pattern
   is bound once its value is known, and before the code in its scope. *)
let rec visit t (e : expr) =
  match e.desc with
  | If_let (p, x, b, alt) ->
      visit t x;
      bind t p x;
      visit_block t b;
      Option.iter (visit t) alt
  | Match (x, arms) ->
      visit t x;
      List.iter
        (fun (a : arm) ->
          bind t a.pattern x;
          Option.iter (visit t) a.guard;
          visit t a.body)
        arms
  | For (p, Iter x, b) ->
      visit t x;
      bind t p x;
      visit_block t b
  | _ ->
      List.iter
        (function Walk.Expr e -> visit t e | Block b -> visit_block t b)
        (Walk.parts e)

and visit_block t b =
  List.iter
    (fun (s : stmt) ->
      List.iter (visit t) (Walk.stmt_exprs s);
      match s.stmt with
      | Let bd -> bind t bd.pattern bd.value
      | Var bd -> bind ~var:true t bd.pattern bd.value
      | Assign (None, { desc = Local v; _ }, value) -> assign t v value
      | Assign _ | Assert _ | Yield _ | Expr _ -> ())
    b

let collect block =
  let t = Hashtbl.create 16 in
  visit_block t block;
  t

let describe_bare = function
  | Place p | Written p ->
      String.concat ""
        (p.root.name
        :: List.map (function P.Field f -> "." ^ f | Index -> "[…]") p.path)
  | Temporary at -> Printf.sprintf "the value made on line %d" at.line

let describe s =
  match s with
  | Place _ | Written _ -> Printf.sprintf "`%s`" (describe_bare s)
  | Temporary _ -> describe_bare s
