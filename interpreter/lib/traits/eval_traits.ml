(* The prelude traits, which run the program's impls or the structural ones
   (traits.prelude-traits, traits.structural-impls and traits.floats), and what builds on them: the keys of maps, and the
   binary operators. *)

open Tast
open Value
open Eval_state
open Eval_types
open Eval_operators
open Eval_targets
module T = Types

let primitive = function
  | Int _ | Float _ | Bool _ | Str _ -> true
  | Tuple _ | List _ | Map _ | Variant _ | Record _ | Fn _ | Iter _ | Window _
  | Deferred _ | Handler _ | Shared _ | Meta _ ->
      false

let ordering c =
  let name = if c < 0 then "Less" else if c > 0 then "Greater" else "Equal" in
  Variant (T.prelude_item name, [])

(* FNV-1a, for the structural hashes, whose values programs can't observe
   (traits.prelude-traits). *)
let fnv = 0xcbf29ce484222325L
let mix h x = Int64.mul (Int64.logxor h x) 0x100000001b3L

let mix_string h s =
  String.fold_left (fun h c -> mix h (Int64.of_int (Char.code c))) h s

(* The prelude traits (traits.prelude-traits and traits.structural-impls). The primitive types have only
   their structural impls, since no module can write others for them. *)

let rec trait_call t fr loc trait name ty values =
  let callee = Trait_method (T.prelude_item trait, name, ty) in
  t.apply t fr loc (target t callee []) values

and equal t fr loc ty a b =
  if primitive a then structural_eq t fr loc ty a b
  else truth (trait_call t fr loc "Eq" "eq" ty [| a; b |])

and order t fr loc ty a b =
  if primitive a then structural_compare t fr loc ty a b
  else
    match trait_call t fr loc "Ord" "compare" ty [| a; b |] with
    | Variant ({ name = "Less"; _ }, _) -> -1
    | Variant ({ name = "Greater"; _ }, _) -> 1
    | _ -> 0

and hash t fr loc ty v =
  if primitive v then structural_hash t fr loc ty v
  else
    match trait_call t fr loc "Hash" "hash" ty [| v |] with
    | Int h -> h
    | _ -> invalid_arg "Eval_traits.hash"

and show t fr loc name ty v =
  if primitive v then structural_show t fr loc name ty v
  else
    match trait_call t fr loc "Show" name ty [| v |] with
    | Str s -> s
    | _ -> invalid_arg "Eval_traits.show"

(* A view has the structural impls of the part it views, which is its value
   (views.functions-of-views). *)
and structural t fr loc name ty values =
  let ty = viewed ty in
  match (name, values) with
  | "eq", [| a; b |] -> Bool (structural_eq t fr loc ty a b)
  | "compare", [| a; b |] -> ordering (structural_compare t fr loc ty a b)
  | "hash", [| v |] -> Int (structural_hash t fr loc ty v)
  | ("show" | "show_nested"), [| v |] ->
      Str (structural_show t fr loc name ty v)
  | _ -> invalid_arg "Eval_traits.structural"

and structural_eq t fr loc ty a b =
  match (a, b) with
  | Int x, Int y -> Int64.equal x y
  | Float x, Float y -> x = y
  | Bool x, Bool y -> x = y
  | Str x, Str y -> String.equal x y
  | Map d, Map e ->
      (* The same entries, in any order (traits.map-equality). *)
      let kty, vty = key_value_types ty in
      Dict.length d = Dict.length e
      && List.for_all
           (fun (k, v) ->
             match lookup t fr loc kty e k with
             | Some (_, w) -> equal t fr loc vty v w
             | None -> false)
           (Dict.entries d)
  | Variant (v, _), Variant (w, _) when v <> w -> false
  | List xs, List ys when Vec.length xs <> Vec.length ys -> false
  | _ ->
      List.for_all2
        (fun (ty, x) (_, y) -> equal t fr loc ty x y)
        (components t ty a) (components t ty b)

and structural_compare t fr loc ty a b =
  let rec lexicographic xs ys =
    match (xs, ys) with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | (ty, x) :: xs, (_, y) :: ys ->
        let c = order t fr loc ty x y in
        if c <> 0 then c else lexicographic xs ys
  in
  match (numeric ty, a, b) with
  | Integer k, Int x, Int y -> Ints.compare k x y
  | _, Float x, Float y -> Floats.total_compare x y
  | _, Bool x, Bool y -> Bool.compare x y
  | _, Str x, Str y -> String.compare x y
  | _, Variant (v, _), Variant (w, _) when v <> w ->
      Int.compare (variant_index t v) (variant_index t w)
  | _ -> lexicographic (components t ty a) (components t ty b)

and structural_hash t fr loc ty v =
  match v with
  | Int x -> mix fnv x
  | Bool b -> mix fnv (if b then 1L else 0L)
  | Str s -> mix_string fnv s
  | _ ->
      let start =
        match v with
        | Variant (item, _) -> mix fnv (Int64.of_int (variant_index t item))
        | List xs -> mix fnv (Int64.of_int (Vec.length xs))
        | _ -> fnv
      in
      List.fold_left
        (fun h (ty, x) -> mix h (hash t fr loc ty x))
        start (components t ty v)

(* The output of std.show-output. *)
and structural_show t fr loc name ty v =
  let nested () =
    List.map
      (fun (ty, x) -> show t fr loc "show_nested" ty x)
      (components t ty v)
  in
  match (numeric ty, v) with
  | Integer k, Int x -> Ints.to_string k x
  | Floating f32, Float x -> Floats.to_string ~f32 x
  | _, Bool b -> Bool.to_string b
  | _, Str s -> if name = "show_nested" then Strings.quote s else s
  | _, Tuple [ _ ] -> "(" ^ List.hd (nested ()) ^ ",)"
  | _, Tuple _ -> "(" ^ String.concat ", " (nested ()) ^ ")"
  | _, List _ -> "[" ^ String.concat ", " (nested ()) ^ "]"
  | _, Map d ->
      let kty, vty = key_value_types ty in
      let entry (k, x) =
        let k = show t fr loc "show_nested" kty k in
        k ^ ": " ^ show t fr loc "show_nested" vty x
      in
      "{" ^ String.concat ", " (List.map entry (Dict.entries d)) ^ "}"
  | _, Variant (item, []) -> item.name
  | _, Variant (item, _) ->
      item.name ^ "(" ^ String.concat ", " (nested ()) ^ ")"
  (* records.field-order *)
  | _, Record (item, fields) when item = T.anonymous ->
      let field (f, _) shown = f ^ ": " ^ shown in
      "{ " ^ String.concat ", " (List.map2 field fields (nested ())) ^ " }"
  | _, Record (item, []) -> item.name ^ " {}"
  | _, Record (item, fields) ->
      let field (f, _) shown = f ^ ": " ^ shown in
      item.name ^ " { "
      ^ String.concat ", " (List.map2 field fields (nested ()))
      ^ " }"
  | _ -> invalid_arg "Eval_traits.structural_show"

(* A map finds a key by hashing it once, then comparing it with each key of
   the same hash, in insertion order (std.maps and std.finding-keys). *)
and lookup t fr loc kty d k =
  let hash = hash t fr loc kty k in
  Dict.find d ~hash ~same:(fun other -> equal t fr loc kty k other)

let insert t fr loc kty d k v =
  let hash = hash t fr loc kty k in
  match Dict.find d ~hash ~same:(fun other -> equal t fr loc kty k other) with
  | Some (stamp, _) -> Dict.set d stamp v
  | None -> Dict.add d ~hash k v

(* [a op b], where [static] is the left operand's type as the program writes
   it, [ty] that type with the body's type arguments, and [right] the right
   operand's type with them. *)
let binary t fr loc (op : Ast.binary) ~static ~right ty a b =
  match op with
  | Eq -> Bool (equal t fr loc ty a b)
  | Ne -> Bool (not (equal t fr loc ty a b))
  | Lt | Le | Gt | Ge -> (
      (* IEEE on floats, and [Ord.compare] on every type that isn't numeric
         where it is written, a type parameter included (traits.operators and traits.floats). *)
      match (T.numeric_name static, a, b) with
      | Some _, Float x, Float y ->
          Bool
            (match op with
            | Lt -> x < y
            | Le -> x <= y
            | Gt -> x > y
            | _ -> x >= y)
      | _ ->
          let c = order t fr loc ty a b in
          Bool
            (match op with
            | Lt -> c < 0
            | Le -> c <= 0
            | Gt -> c > 0
            | _ -> c >= 0))
  | And | Or -> invalid_arg "Eval_traits.binary"
  | Shl | Shr -> shift fr loc op ty ~amount:right a b
  | _ -> arithmetic fr loc op ty a b
