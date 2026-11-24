(* meta.fresh-types: the type of a field, an element or a payload is a fresh
   type of the arm or the loop body that reads it, and a value whose type
   holds one can't leave it (E0351). *)

module T = Types
open Check_state

(* Whether [a] and [b] could be one type, each variable standing for any
   type. Where unification refused them, a rigid type that one holds would
   have reached a variable made before it. *)
let rec could_be a b =
  match (T.resolve a, T.resolve b) with
  | (Var _ as x), t | t, (Var _ as x) -> (
      match (T.unsolved x, t) with
      | Some { kind = Int_literal | Float_literal; _ }, Con (i, []) ->
          Check_unify.numeric i
      | Some { kind = Int_literal | Float_literal; _ }, Var _ -> true
      | Some { kind = Int_literal | Float_literal; _ }, _ -> false
      | _ -> true)
  | Error, _ | _, Error -> true
  | Con (i, xs), Con (j, ys) -> i = j && all xs ys
  | Tuple xs, Tuple ys -> all xs ys
  | Record xs, Record ys ->
      List.map fst xs = List.map fst ys
      && all (List.map snd xs) (List.map snd ys)
  | Param p, Param q -> p.id = q.id
  | Value x, Value y -> x = y
  | App (f, xs), App (g, ys) -> could_be f g && all xs ys
  | Fn (ps, r, _), Fn (qs, s, _) ->
      all (List.map snd ps) (List.map snd qs) && could_be r s
  | _ -> false

and all xs ys = List.length xs = List.length ys && List.for_all2 could_be xs ys

let fresh_of t = List.find_opt Meta.is_fresh (T.type_params t)

let leave st loc ty (v : Hir.var) =
  error st Code.e0351 loc
    "this value, of type `%s`, would leave the code that knows `%s`, the type \
     of a part of `%s`'s shape, which nothing outside it can name"
    (show ty) v.name
    (Option.fold ~none:"?" ~some:show (Meta.origin v))

(* E0351 at [loc] where [actual] would be [expected] but that a fresh type
   one of them holds would decide a type that inference left open outside
   its arm or loop body. *)
let leaves st loc ~expected actual =
  match (fresh_of actual, fresh_of expected) with
  | (Some v, _ | None, Some v) when could_be expected actual ->
      leave st loc actual v;
      true
  | _ -> false

(* The value of an arm, or of an [if let]'s first branch, that decides the
   type of its form: E0351 when it holds a fresh type that its pattern, or
   code inside it, made after the mark [m]. *)
let arm_value st m (body : Tast.expr) =
  match Meta.fresh_in m body.ty with
  | Some v ->
      leave st body.loc body.ty v;
      { body with ty = T.Error }
  | None -> body

(* A raised value whose type holds a fresh type leaves its arm. *)
let raised st (value : Tast.expr) =
  match fresh_of value.ty with
  | Some v ->
      leave st value.loc value.ty v;
      false
  | None -> true
