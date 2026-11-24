(* tests.generable-types and tests.minimal-values. *)

module T = Types

type unfit = Function | No_values of T.ty | Key of T.ty | Infinite

type node =
  | Bool
  | Int of Ints.kind
  | Float of bool
  | Str
  | Unit
  | Tuple of int list
  | List of int
  | Map of int * int
  | Record of Hir.item * (string * int) list
  | Variants of (Hir.item * int list) list

type graph = { nodes : node array; tys : T.ty array; depths : int array }

exception Unfit of unfit

(* A text that names a type uniquely, its declared types by their homes. *)
let key ty =
  let b = Buffer.create 32 in
  let rec go ty =
    match T.resolve ty with
    | T.Con (item, args) ->
        Buffer.add_string b item.home;
        Buffer.add_char b '.';
        Buffer.add_string b item.name;
        if args <> [] then list '<' args '>'
    | Tuple ts -> list '(' ts ')'
    | Record fields ->
        Buffer.add_string b (String.concat "," (List.map fst fields));
        list '{' (List.map snd fields) '}'
    | Fn _ | Forall _ | Handler _ -> Buffer.add_string b "fn"
    | Param _ | App _ | Spread _ | Var _ | Error -> Buffer.add_char b '?'
    | Value v -> Buffer.add_string b v
  and list opening ts closing =
    Buffer.add_char b opening;
    List.iteri
      (fun i t ->
        if i > 0 then Buffer.add_char b ',';
        go t)
      ts;
    Buffer.add_char b closing
  in
  go ty;
  Buffer.contents b

let subst (info : Env.type_info) args t =
  T.subst (List.combine info.params args) [] t

let prelude ty name =
  match T.resolve ty with
  | T.Con (item, _) -> item = T.prelude_item name
  | _ -> false

let implements env ty name =
  Env.implements env [] ty (T.prelude_item name) = Yes

(* The node of a type, before its components are numbered, and their types. *)
let shape env ty =
  let scalar node = (`Scalar node, []) in
  match T.resolve ty with
  | T.Con (item, args) -> (
      match (Ints.of_name item.name, Env.type_info env item, args) with
      | Some k, Some { def = Builtin; _ }, _ -> scalar (Int k)
      | _ when prelude ty "f32" -> scalar (Float true)
      | _ when prelude ty "f64" -> scalar (Float false)
      | _ when prelude ty "bool" -> scalar Bool
      | _ when prelude ty "str" -> scalar Str
      | _, Some { def = Builtin; _ }, [ elem ] when prelude ty "List" ->
          (`List, [ elem ])
      | _, Some { def = Builtin; _ }, [ k; v ] when prelude ty "Map" ->
          if not (implements env k "Eq" && implements env k "Hash") then
            raise (Unfit (Key k));
          (`Map, [ k; v ])
      | _, Some ({ def = Record fields; _ } as info), _ ->
          ( `Record (item, List.map fst fields),
            List.map (fun (_, t) -> subst info args t) fields )
      | _, Some ({ def = Variants vs; _ } as info), _ ->
          let payloads =
            List.map (fun (_, p) -> List.map (subst info args) p) vs
          in
          let names =
            List.map (fun (n, p) -> ({ item with name = n }, List.length p)) vs
          in
          (`Variants names, List.concat payloads)
      | _ -> (`Variants [], []))
  | Tuple [] -> scalar Unit
  | Tuple ts -> (`Tuple, ts)
  (* records.field-order: an anonymous record's fields, in alphabetical order. *)
  | Record fields ->
      (`Record (T.anonymous, List.map fst fields), List.map snd fields)
  | Fn _ | Forall _ | Handler _ -> raise (Unfit Function)
  | Param _ | App _ | Spread _ | Var _ | Value _ | Error -> scalar Unit

let rec take n xs =
  match (n, xs) with
  | 0, _ | _, [] -> ([], xs)
  | n, x :: rest ->
      let a, b = take (n - 1) rest in
      (x :: a, b)

(* Every type that [roots] hold, numbered in the order a walk meets them. *)
let explore env roots =
  let index = Hashtbl.create 16 and found = ref [] and count = ref 0 in
  let rec visit ty =
    let k = key ty in
    match Hashtbl.find_opt index k with
    | Some i -> i
    | None ->
        let i = !count in
        incr count;
        Hashtbl.add index k i;
        let kind, parts = shape env ty in
        let slots = List.map visit parts in
        let node =
          match kind with
          | `Scalar node -> node
          | `List -> List (List.hd slots)
          | `Map -> Map (List.nth slots 0, List.nth slots 1)
          | `Tuple -> Tuple slots
          | `Record (item, fields) -> Record (item, List.combine fields slots)
          | `Variants names ->
              let rest = ref slots in
              Variants
                (List.map
                   (fun (v, n) ->
                     let mine, others = take n !rest in
                     rest := others;
                     (v, mine))
                   names)
        in
        found := (i, ty, node) :: !found;
        i
  in
  let params = List.map visit roots in
  let sorted =
    List.sort compare (List.map (fun (i, t, n) -> (i, (t, n))) !found)
  in
  let tys = Array.of_list (List.map (fun (_, (t, _)) -> t) sorted) in
  let nodes = Array.of_list (List.map (fun (_, (_, n)) -> n) sorted) in
  (nodes, tys, params)

let infinite = max_int

(* tests.minimal-values: the least depths, found by lowering them from [infinite] until
   none changes. *)
let depths nodes =
  let d =
    Array.map
      (function Tuple _ | Record _ | Variants _ -> infinite | _ -> 0)
      nodes
  in
  let deepest slots =
    List.fold_left
      (fun m s ->
        if m = infinite || d.(s) = infinite then infinite else max m d.(s))
      0 slots
  in
  let changed = ref true in
  while !changed do
    changed := false;
    Array.iteri
      (fun i node ->
        let next =
          match node with
          | Tuple slots ->
              if deepest slots = infinite then infinite else 1 + deepest slots
          | Record (_, fields) ->
              let h = deepest (List.map snd fields) in
              if h = infinite then infinite else 1 + h
          | Variants vs ->
              let least =
                List.fold_left (fun m (_, p) -> min m (deepest p)) infinite vs
              in
              if least = infinite then infinite else 1 + least
          | _ -> d.(i)
        in
        if next < d.(i) then (
          d.(i) <- next;
          changed := true))
      nodes
  done;
  d

let build env roots =
  match
    if Prop_growth.infinite env roots then raise (Unfit Infinite);
    explore env roots
  with
  | exception Unfit u -> Error u
  | nodes, tys, params -> (
      let depths = depths nodes in
      let empty = ref None in
      Array.iteri
        (fun i d -> if d = infinite && !empty = None then empty := Some i)
        depths;
      match !empty with
      | Some i -> Error (No_values tys.(i))
      | None -> Ok ({ nodes; tys; depths }, params))

let unfit env ty =
  if T.mentions_error ty then None
  else match build env [ ty ] with Ok _ -> None | Error u -> Some u

let height g payload =
  List.fold_left
    (fun m s ->
      if m = infinite || g.depths.(s) = infinite then infinite
      else max m g.depths.(s))
    0 payload

let live g vs = List.filter (fun (_, p) -> height g p <> infinite) vs

let nearest g vs =
  let vs = live g vs in
  let least = List.fold_left (fun m (_, p) -> min m (height g p)) infinite vs in
  List.filter (fun (_, p) -> height g p = least) vs
