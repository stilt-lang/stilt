(* tests.shrink-candidates and tests.property-verdict; std.show-output. *)

open Value
module P = Prop_types

let rec show (g : P.graph) i v =
  let nested slots values = List.map2 (show g) slots values in
  match (g.nodes.(i), v) with
  | Int k, Int x -> Ints.to_string k x
  | Float f32, Float x -> Floats.to_string ~f32 x
  | Bool, Bool b -> Bool.to_string b
  | Str, Str s -> Strings.quote s
  | Unit, _ -> "()"
  | Tuple [ s ], Tuple [ x ] -> "(" ^ show g s x ^ ",)"
  | Tuple slots, Tuple xs -> "(" ^ String.concat ", " (nested slots xs) ^ ")"
  | List s, List xs ->
      "[" ^ String.concat ", " (List.map (show g s) (Vec.to_list xs)) ^ "]"
  | Map (ks, vs), Map d ->
      let entry (k, x) = show g ks k ^ ": " ^ show g vs x in
      "{" ^ String.concat ", " (List.map entry (Dict.entries d)) ^ "}"
  | Variants _, Variant (item, []) -> item.name
  | Variants vs, Variant (item, xs) ->
      let payload = List.assoc item vs in
      item.name ^ "(" ^ String.concat ", " (nested payload xs) ^ ")"
  | Record (item, []), _ -> item.name ^ " {}"
  | Record (item, fields), Record (_, xs) ->
      let field (f, s) (_, x) = f ^ ": " ^ show g s x in
      item.name ^ " { " ^ String.concat ", " (List.map2 field fields xs) ^ " }"
  | _ -> invalid_arg "Prop_show.show"

let rec identity v =
  let all xs = String.concat "," (List.map identity xs) in
  match v with
  | Int x -> "i" ^ Int64.to_string x
  | Float x -> "f" ^ Int64.to_string (Int64.bits_of_float x)
  | Bool b -> if b then "t" else "f"
  | Str s -> "s" ^ string_of_int (String.length s) ^ ":" ^ s
  | Tuple xs -> "(" ^ all xs ^ ")"
  | List xs -> "[" ^ all (Vec.to_list xs) ^ "]"
  | Map d ->
      "{"
      ^ all (List.concat_map (fun (k, x) -> [ k; x ]) (Dict.entries d))
      ^ "}"
  | Variant (item, xs) -> item.home ^ "." ^ item.name ^ "(" ^ all xs ^ ")"
  | Record (_, fields) -> "{" ^ all (List.map snd fields) ^ "}"
  | Fn _ | Iter _ | Window _ | Deferred _ | Handler _ | Shared _ | Meta _ ->
      invalid_arg "Prop_show.identity"
