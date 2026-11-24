(* The shapes of types (meta.shapes): the first case that fits a type,
   and the types it holds. *)

module T = Types

type case =
  | Leaf of string
  | Holds of string * T.ty list
  | Fields of string * (string * T.ty) list
  | Cases of (Hir.item * T.ty list) list

let name = function
  | Leaf n | Holds (n, _) | Fields (n, _) -> n
  | Cases _ -> "Variants"

let parts = function
  | Leaf _ -> []
  | Holds (_, ts) -> ts
  | Fields (_, fields) -> List.map snd fields
  | Cases variants -> List.concat_map snd variants

let sub (info : Env.type_info) args t =
  if List.length info.params = List.length args then
    T.subst (List.combine info.params args) [] t
  else T.Error

(* A declared record, in the order of its declaration, and a declared
   variant type, but for [Shape], a native type, which has none (meta.types-without-shape). *)
let declared env (item : Hir.item) args =
  match Env.type_info env item with
  | Some ({ def = Record fields; _ } as info) ->
      Some
        (Fields ("Record", List.map (fun (n, t) -> (n, sub info args t)) fields))
  | Some ({ def = Variants vs; _ } as info) when item <> Meta.shape ->
      Some
        (Cases
           (List.map
              (fun (n, payload) ->
                ({ item with name = n }, List.map (sub info args) payload))
              vs))
  | _ -> None

let prelude env name args =
  match (name, args) with
  | n, [] when List.mem n T.integer_types -> Some (Leaf "Int")
  | n, [] when List.mem n T.float_types -> Some (Leaf "Float")
  | "bool", [] -> Some (Leaf "Bool")
  | "str", [] -> Some (Leaf "Str")
  | ("Option" | "List" | "Set"), [ e ] -> Some (Holds (name, [ e ]))
  | "Map", [ k; v ] -> Some (Holds ("Map", [ k; v ]))
  | _ -> declared env { home = "std.prelude"; name } args

let case_of env ty =
  match T.resolve ty with
  | Con ({ home = "std.prelude"; name }, args) -> prelude env name args
  | Con ({ home = "std.array"; name = "Array" }, [ e; _ ]) ->
      Some (Holds ("Array", [ e ]))
  | Con (item, args) -> declared env item args
  | Tuple [] -> Some (Leaf "Unit")
  | Tuple ts when not (List.exists Packs.is_spread ts) ->
      Some (Fields ("Tuple", List.mapi (fun i t -> (string_of_int i, t)) ts))
  (* records.field-order: in the alphabetical order of their names. *)
  | Record fields -> Some (Fields ("Record", fields))
  | Tuple _ | Param _ | App _ | Spread _ | Fn _ | Forall _ | Handler _ | Var _
  | Value _ | Error ->
      None

let payload env ty case =
  match (List.assoc_opt case (Meta.cases ty), case_of env ty) with
  | Some payload, Some (Holds (_, held)) ->
      let rec pair vars ts =
        match (vars, ts) with
        | v :: vars, t :: ts -> (v, t) :: pair vars ts
        | _ -> []
      in
      let vars =
        match held with
        | [ _; _ ] -> List.tl Meta.placeholders
        | _ -> Meta.placeholders
      in
      Some (T.subst (pair vars held) [] payload)
  | payload, _ -> payload

let describe ty = Types_show.to_string (T.zonk ty)
