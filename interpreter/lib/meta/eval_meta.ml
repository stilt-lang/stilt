(* Reflection at run time (meta.shapes, meta.fresh-types and meta.bound-tests): the shapes of the concrete types that a
   body's type arguments give, bound tests, the accessors of
   [std.meta], and the fresh types that arms and loops bind. A shape's
   accessors are tokens that their types describe: a field or a case is its
   position, and every other accessor is [()]. *)

open Value
open Eval_state
open Eval_types
module T = Types
module S = Meta_shapes

let case_of t ty =
  match S.case_of t.env ty with
  | Some c -> c
  | None -> invalid_arg ("Eval_meta: a type without a shape: " ^ S.describe ty)

(* meta.fresh-types: binds the fresh types that the pattern type [pty] holds to the
   parts of [concrete] they stand for, in the frame's type arguments. *)
let bind fr pty concrete =
  let fresh = List.filter Meta.is_fresh (T.type_params pty) in
  let others = List.filter (fun (v, _) -> not (List.mem v fresh)) fr.tenv in
  match Eval_targets.matching (T.subst others [] pty) concrete [] with
  | [] -> ()
  | bound ->
      fr.tenv <- List.filter (fun (v, _) -> List.mem v fresh) bound @ fr.tenv

(* The pattern of a case of [Shape<T>], of type [shape], binds its payload's
   fresh types to the types that [T] holds. *)
let bind_case t fr shape (item : Hir.item) (ps : Tast.pattern list) =
  match (T.resolve (concrete fr shape), ps) with
  | Con (_, [ ty ]), [ p ] ->
      Option.iter (bind fr p.pty) (S.payload t.env ty item.name)
  | _ -> ()

(* meta.bound-tests: whether the concrete type has an impl of each bound, with its
   arguments, whose own bounds hold. *)
let implements t ty (bounds : T.bound list) =
  List.for_all
    (fun (b : T.bound) ->
      Env.implements t.env [] ty b.trait = Env.Yes
      && (b.args = []
         ||
         match Env.trait_args t.env [] ty b.trait with
         | Some args -> Env_signatures.equal_list args b.args
         | None -> false))
    bounds

let reflect t fr (r : Tast.reflect) =
  match r with
  | Shape_of ty ->
      let case = case_of t (concrete fr ty) in
      Variant (Meta.item (S.name case), [ unit ])
  | Name_of ty -> Str (S.describe (concrete fr ty))
  | Implements (ty, bounds) ->
      Bool
        (implements t (concrete fr ty)
           (List.map
              (fun (b : T.bound) ->
                { b with args = List.map (concrete fr) b.args })
              bounds))

(* The fields of a tuple or a record type, and the variants of a variant
   type, in order. *)
let fields t ty =
  match case_of t ty with
  | Fields (_, fields) -> fields
  | _ -> invalid_arg "Eval_meta.fields"

let variants t ty =
  match case_of t ty with
  | Cases variants -> variants
  | _ -> invalid_arg "Eval_meta.variants"

(* meta.fields and meta.variant-cases: a [for] over the fields or the cases of [T] binds each, in
   order, with the fresh type of its field or its payload. *)
let iterated ty =
  match T.resolve ty with
  | Con (item, [ _ ]) -> item = Meta.item "Fields" || item = Meta.item "Cases"
  | _ -> false

let iterate t fr ty (p : Tast.pattern) each =
  let elements =
    match T.resolve ty with
    | Con ({ name = "Fields"; _ }, [ of_ ]) ->
        List.map (fun (_, f) -> Meta.ty "Field" [ of_; f ]) (fields t of_)
    | Con (_, [ of_ ]) ->
        List.map
          (fun (_, payload) -> Meta.ty "Case" [ of_; T.Tuple payload ])
          (variants t of_)
    | _ -> invalid_arg "Eval_meta.iterate"
  in
  let rec go i = function
    | [] -> ()
    | element :: rest ->
        bind fr p.pty element;
        if each (Int (Int64.of_int i)) then go (i + 1) rest
  in
  go 0 elements
