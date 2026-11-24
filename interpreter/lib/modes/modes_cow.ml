(* Recursive types (facts.allocation) and copy-on-write types (modes.copy-on-write-types). *)

module T = Types

(* The declared types that a type names, at any depth. *)
let rec named (ty : T.ty) =
  match T.resolve ty with
  | Con (item, args) -> item :: List.concat_map named args
  | Tuple ts -> List.concat_map named ts
  | Record fields -> List.concat_map (fun (_, t) -> named t) fields
  | App (h, ts) -> List.concat_map named (h :: ts)
  | Spread (_, t) -> named t
  | Fn (ps, ret, row) ->
      List.concat_map (fun (_, t) -> named t) ps
      @ named ret
      @ Option.fold ~none:[] ~some:named row.raise
  | Forall p -> named p.body
  | Handler h -> List.concat_map named (h.hargs @ Option.to_list h.answer)
  | Param _ | Var _ | Value _ | Error -> []

(* The types that the fields and payloads of a declared type name. *)
let neighbours env item =
  match Env.type_info env item with
  | Some { def = Record fields; _ } ->
      List.concat_map (fun (_, t) -> named t) fields
  | Some { def = Variants vs; _ } ->
      List.concat_map (fun (_, p) -> List.concat_map named p) vs
  | Some { def = Builtin; _ } | None -> []

let recursive env item =
  let rec reach seen = function
    | [] -> false
    | next :: rest when List.mem next seen -> reach seen rest
    | next :: rest ->
        next = item || reach (next :: seen) (neighbours env next @ rest)
  in
  reach [] (neighbours env item)

(* The types that the fields and payloads of [item] applied to [args] hold,
   and the elements of an array, which it holds inline as a record holds its
   fields (generics.array-effects). *)
let held env (item : Hir.item) args =
  match (Env.type_info env item, args) with
  | Some { def = Builtin; _ }, [ elem; _ ]
    when item.home = "std.array" && item.name = "Array" ->
      [ elem ]
  | None, _ -> []
  | Some info, _ ->
      let subst t =
        if List.length info.params = List.length args then
          T.subst (List.combine info.params args) [] t
        else T.Error
      in
      List.map subst
        (match info.def with
        | Record fields -> List.map snd fields
        | Variants vs -> List.concat_map snd vs
        | Builtin -> [])

(* A type parameter may stand for a copy-on-write type, so it counts as one,
   as the facts are conservative (modes.shared-writes). A declared type that isn't
   recursive holds a finite tree of types, so the walk ends. *)
let rec is_cow env (ty : T.ty) =
  match T.resolve ty with
  | Con (item, args) ->
      List.mem item (List.map T.prelude_item [ "str"; "List"; "Map" ])
      ||
      let parts = held env item args in
      parts <> [] && (recursive env item || List.exists (is_cow env) parts)
  | Tuple ts -> List.exists (is_cow env) ts
  | Record fields -> List.exists (fun (_, t) -> is_cow env t) fields
  | Fn _ | Forall _ | Handler _ | Param _ | App _ | Spread _ -> true
  | Var _ | Value _ | Error -> false

(* A type that may stand for any type: a part of it may be a part of anything
   (modes.call-stores). *)
let stands_for_any (ty : T.ty) =
  match ty with
  | Param _ | App _ | Spread _ | Forall _ | Handler _ -> true
  | _ -> false

(* modes.call-stores: the parts of a value of [ty], each a copy-on-write type:
   the type itself, and the parts of what it holds, those of the values that a
   function's calls give back or write through its [inout] parameters
   included. A type met again adds nothing, and a recursive type's fields and
   payloads are walked the first time its declaration is met, so the walk ends,
   though a type may hold its own declaration at other arguments. *)
let parts env ty =
  let expanded = Hashtbl.create 8 in
  let rec go found ty =
    let ty = T.resolve ty in
    if List.mem ty found || not (is_cow env ty) then found
    else
      let inner =
        match ty with
        | Con (item, args) -> (
            match Env.type_info env item with
            | Some { def = Builtin; _ } -> args
            | _ when Hashtbl.mem expanded item -> args
            | _ ->
                if recursive env item then Hashtbl.replace expanded item ();
                held env item args)
        | Tuple ts -> ts
        | Record fields -> List.map snd fields
        | Fn (ps, ret, _) ->
            ret
            :: List.filter_map
                 (fun (m, t) -> if m = Ast.Inout then Some t else None)
                 ps
        | _ -> []
      in
      List.fold_left go (ty :: found) inner
  in
  go [] ty

(* modes.call-stores: whether a call may store an argument of type [from] in a
   value of one of [targets]: a part of one is a part of the other, or stands
   for any type, or the target's part is a function type, whose closures may
   capture anything. *)
let may_store env from targets =
  let sources = parts env from in
  sources <> []
  && List.exists
       (fun target ->
         List.exists
           (fun q ->
             (match q with T.Fn _ -> true | _ -> stands_for_any q)
             || List.exists (fun p -> p = q || stands_for_any p) sources)
           (parts env target))
       targets
