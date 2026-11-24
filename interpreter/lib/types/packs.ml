(* Packs and spreads in types (variadics.type-spreads and variadics.pack-tuples). *)

open Types

let is_spread = function Spread _ -> true | _ -> false

let rec mentions_pack pack t =
  same_pack pack t
  ||
  match resolve t with
  | Var _ | Param _ | Value _ | Error -> false
  | Con (_, ts) | Tuple ts | App (_, ts) -> List.exists (mentions_pack pack) ts
  | Record fields -> List.exists (fun (_, t) -> mentions_pack pack t) fields
  | Spread (p, b) -> mentions_pack pack p || mentions_pack pack b
  | Fn (ps, ret, _) ->
      List.exists (fun (_, t) -> mentions_pack pack t) ps
      || mentions_pack pack ret
  | Handler h ->
      List.exists (mentions_pack pack) (h.hargs @ Option.to_list h.answer)
  | Forall p -> mentions_pack pack p.body

(* variadics.pack-tuples: the pack and the element of a pack tuple, a tuple whose one
   element is a spread. *)
let pack_tuple t =
  match resolve t with
  | Tuple [ Spread (pack, body) ] -> Some (pack, body)
  | _ -> None

let has_spread t =
  match resolve t with Tuple ts -> List.exists is_spread ts | _ -> false
