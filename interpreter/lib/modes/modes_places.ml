(* Places, and the variables that code binds and modifies. *)

open Tast

(* Places (modes.places), with each index kept only as a position. *)
type step = Field of string | Index
type place = { root : Hir.var; path : step list }

let place (e : expr) =
  let rec go (e : expr) path =
    match e.desc with
    | Local v -> Some { root = v; path }
    | Field (base, name) -> go base (Field name :: path)
    | Tuple_field (base, i) -> go base (Field (string_of_int i) :: path)
    | Index (base, _) -> go base (Index :: path)
    | _ -> None
  in
  go e []

let fields p =
  List.filter_map (function Field f -> Some f | Index -> None) p.path

let rec is_prefix a b =
  match (a, b) with
  | [], _ -> true
  | x :: a, y :: b -> x = y && is_prefix a b
  | _ :: _, [] -> false

(* shared.names-that-may-be-one-place: each name of the [when]s around the code being checked,
   by its variable, with the first name of its [when] whose value has the
   same type, which stands for both. *)
let aliases : (int, int) Hashtbl.t = Hashtbl.create 8

let root (v : Hir.var) =
  Option.value ~default:v.id (Hashtbl.find_opt aliases v.id)

let holding (names : (Hir.var * ty) list) check =
  let rec first = function
    | [] -> ()
    | ((v : Hir.var), ty) :: rest ->
        let same, others =
          List.partition (fun (_, t) -> Types.zonk t = Types.zonk ty) rest
        in
        List.iter
          (fun ((w : Hir.var), _) -> Hashtbl.replace aliases w.id v.id)
          same;
        first others
  in
  first names;
  Fun.protect
    ~finally:(fun () ->
      List.iter (fun ((v : Hir.var), _) -> Hashtbl.remove aliases v.id) names)
    check

(* modes.overlap *)
let overlap a b =
  root a.root = root b.root
  &&
  let fa = fields a and fb = fields b in
  is_prefix fa fb || is_prefix fb fa

(* The expressions a place evaluates to find its target: its indexes, in
   order. *)
let place_parts (e : expr) =
  let rec go (e : expr) parts =
    match e.desc with
    (* A projection's arguments are its call's to weigh (projections.when-projection-runs). *)
    | Local _ | Project _ -> parts
    | Field (base, _) | Tuple_field (base, _) -> go base parts
    | Index (base, i) -> go base (i :: parts)
    | _ -> e :: parts
  in
  go e []

let rec pattern_vars (p : pattern) =
  match p.pat with
  | P_bind v -> [ v.id ]
  | P_list (ps, Rest_bind v) -> v.id :: List.concat_map pattern_vars ps
  | P_tuple ps | P_variant (_, ps) | P_list (ps, _) | P_or ps ->
      List.concat_map pattern_vars ps
  | P_record fields -> List.concat_map (fun (_, q) -> pattern_vars q) fields
  | P_wild | P_int _ | P_str _ | P_bool _ | P_const _ | P_error -> []

(* modes.what-can-be-modified: the variables a body declares with [var], outside the closures in
   it. *)
let rec var_bindings block =
  List.concat_map
    (fun (s : stmt) ->
      (match s.stmt with Var b -> pattern_vars b.pattern | _ -> [])
      @ List.concat_map expr_var_bindings (Walk.stmt_exprs s))
    block

and expr_var_bindings (e : expr) =
  match e.desc with
  | Closure _ -> []
  (* shared.when: a [when]'s names are writable as a [var] is. *)
  | When (names, b) ->
      List.map (fun (_, (v : Hir.var)) -> v.id) names
      @ List.concat_map expr_var_bindings (List.map fst names)
      @ var_bindings b
  | _ ->
      List.concat_map
        (function
          | Walk.Expr e -> expr_var_bindings e | Block b -> var_bindings b)
        (Walk.parts e)

let inout_params params =
  List.filter_map
    (fun (mode, v) -> if mode = Ast.Inout then Some v else None)
    params
