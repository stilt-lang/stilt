(* Whether a type implements a trait, through an impl the program writes or
   structurally (traits.method-resolution, traits.structural-impls and traits.floats; std.map-key-bounds and traits.hash-follows-written-eq). *)

module T = Types
open Env_tables

type answer = Yes | No | Unknown

let all answers =
  if List.mem No answers then No
  else if List.mem Unknown answers then Unknown
  else Yes

let is_prelude (item : Hir.item) name = item = T.prelude_item name

(* Substitutes the type's parameters by [args] in [t]. *)
let instantiate (info : type_info) args t =
  if List.length info.params <> List.length args then T.Error
  else T.subst (List.combine info.params args) [] t

let bound_of bounds (p : Hir.var) trait =
  List.find_map
    (fun ((v : Hir.var), bs) ->
      if v.id = p.id then List.find_opt (fun (b : bound) -> b.trait = trait) bs
      else None)
    bounds

(* traits.trait-arguments: the substitution that applies [impl] to [args], the type
   arguments of its type constructor: the generics its type names, then
   those that its member types imply, which the impls of their bounds
   give. *)
let rec impl_subst env bounds (impl : impl) args =
  let params = match impl.self_ty with Con (_, ps) -> ps | _ -> [] in
  let direct =
    if List.length params <> List.length args then []
    else
      List.filter_map
        (fun (param, arg) ->
          match param with T.Param v -> Some (v, arg) | _ -> None)
        (List.combine params args)
  in
  let bound_in sub (v : Hir.var) =
    List.exists (fun ((w : Hir.var), _) -> w.id = v.id) sub
  in
  let from_bound ty sub (b : bound) =
    match trait_args env bounds ty b.trait with
    | Some actual when List.length actual = List.length b.args ->
        List.fold_left2
          (fun sub pattern arg ->
            match pattern with
            | T.Param p when not (bound_in sub p) -> sub @ [ (p, arg) ]
            | _ -> sub)
          sub b.args actual
    | _ -> sub
  in
  List.fold_left
    (fun sub ((v : Hir.var), bs) ->
      match List.find_opt (fun ((w : Hir.var), _) -> w.id = v.id) sub with
      | Some (_, ty) -> List.fold_left (from_bound ty) sub bs
      | None -> sub)
    direct impl.generics

(* traits.trait-arguments and traits.bound-arguments: the arguments that the impl of [trait] for [ty]
   gives the trait's parameters, or that a bound of a type parameter gives
   them. A structural impl's trait has none. *)
and trait_args env bounds ty trait =
  let structural = if List.mem trait trait_bounds then Some [] else None in
  match T.resolve ty with
  | Param p | App (Param p, _) ->
      Option.map (fun (b : bound) -> b.args) (bound_of bounds p trait)
  | Con (item, targs) -> (
      match trait_impl env ~trait item with
      | Some impl ->
          let sub = impl_subst env bounds impl targs in
          Some (List.map (T.subst sub []) impl.trait_args)
      | None -> structural)
  | Tuple _ | Record _ -> structural
  | App _ | Spread _ | Fn _ | Forall _ | Handler _ | Var _ | Value _ | Error ->
      None

let rec has_var t =
  match T.resolve t with
  | Var _ -> true
  | Con (_, ts) | Tuple ts -> List.exists has_var ts
  | Record fields -> List.exists (fun (_, t) -> has_var t) fields
  | App (h, ts) -> List.exists has_var (h :: ts)
  | Spread (p, t) -> has_var p || has_var t
  | Fn (ps, r, _) -> List.exists (fun (_, t) -> has_var t) ps || has_var r
  | Handler h -> List.exists has_var (h.hargs @ Option.to_list h.answer)
  | Forall p -> has_var p.body
  | Param _ | Value _ | Error -> false

(* Whether the arguments a type's impl gives a trait are a bound's. *)
let same_args expected actual =
  if List.exists has_var (expected @ actual) then Unknown
  else if Env_signatures.equal_list expected actual then Yes
  else No

let rec implements_in env bounds visiting ty trait =
  let structural = List.mem trait trait_bounds in
  let each ts =
    all (List.map (fun t -> implements_in env bounds visiting t trait) ts)
  in
  match T.resolve ty with
  | Error -> Yes
  | Var _ -> Unknown
  | Param p -> if Option.is_some (bound_of bounds p trait) then Yes else No
  | Fn _ | Forall _ | App _ | Handler _ -> No
  (* A value argument holds no value of its own (generics.array-traits). *)
  | Value _ -> Yes
  | Tuple ts -> if structural then each ts else No
  (* records.field-order *)
  | Record fields -> if structural then each (List.map snd fields) else No
  (* variadics.packs and variadics.pack-tuples: a spread meets a bound when each of its elements
     does, which a pack's bound says of a pack's. *)
  | Spread (pack, body) -> (
      match T.resolve pack with
      | Tuple es -> each (List.map (T.element pack body) es)
      | Var _ -> Unknown
      | _ -> implements_in env bounds visiting body trait)
  | Con (item, args) -> (
      match trait_impl env ~trait item with
      | Some impl -> through_impl env bounds visiting impl args
      | None when not structural -> No
      (* traits.hash-follows-written-eq: a written [Eq] takes the automatic [Hash] away. *)
      | None
        when is_prelude trait "Hash"
             && Option.is_some
                  (trait_impl env ~trait:(T.prelude_item "Eq") item) ->
          No
      | None when List.mem (item, trait) visiting -> Yes
      | None -> structurally env bounds visiting item args trait each)

(* Whether the type arguments [args] meet the bounds of the generics of
   [impl], the impl that the program writes for their type. *)
and through_impl env bounds visiting (impl : impl) args =
  let sub = impl_subst env bounds impl args in
  let meets arg (b : bound) =
    let expected = List.map (T.subst sub []) b.args in
    all
      [
        implements_in env bounds visiting arg b.trait;
        (match trait_args env bounds arg b.trait with
        | Some actual when List.length actual = List.length expected ->
            same_args expected actual
        | Some _ -> No
        | None -> Unknown);
      ]
  in
  all
    (List.concat_map
       (fun ((v : Hir.var), bs) ->
         match List.find_opt (fun ((w : Hir.var), _) -> w.id = v.id) sub with
         | Some (_, arg) -> List.map (meets arg) bs
         | None -> [])
       impl.generics)

(* Whether the type constructor [item], applied to [args], implements the
   structural [trait] without an impl, through what its values hold. *)
and structurally env bounds visiting item args trait each =
  match type_info env item with
  | None -> Yes
  (* meta.std-meta: a shape, a native variant type, has no written representation, so it has
     none of the structural traits, whatever its cases hold. *)
  | Some _ when item = Meta.shape -> No
  (* std.map-key-bounds: comparing maps finds keys, so it needs the key type's
     [Hash] too. *)
  | Some { def = Builtin; _ } when item.name = "Map" && is_prelude trait "Eq" ->
      all
        [
          each args;
          implements_in env bounds visiting (List.hd args)
            (T.prelude_item "Hash");
        ]
  | Some { def = Builtin; _ } -> builtin item args trait each
  | Some ({ def = Record fields; _ } as info) ->
      let visiting = (item, trait) :: visiting in
      all
        (List.map
           (fun (_, t) ->
             implements_in env bounds visiting (instantiate info args t) trait)
           fields)
  | Some ({ def = Variants vs; _ } as info) ->
      let visiting = (item, trait) :: visiting in
      all
        (List.concat_map
           (fun (_, payload) ->
             List.map
               (fun t ->
                 implements_in env bounds visiting (instantiate info args t)
                   trait)
               payload)
           vs)

and builtin item args trait each =
  if builtin_has item trait then each (held_types item args) else No

(* generics.array-traits: an array holds values of its element type, whatever its
   size. *)
and held_types (item : Hir.item) args =
  match ((item.home, item.name), args) with
  | ("std.array", "Array"), [ elem; _ ] -> [ elem ]
  | _ -> args

(* traits.structural-impls and traits.floats: floats have no [Hash], and maps no [Ord] or
   [Hash]. A view has each wherever the type it views has it, and an iterator
   none (views.functions-of-views and views.iterator-traits). A [Lazy] has none either, since each
   would compute it unseen (polymorphism.lazy-unobservable), and a shape none
   (meta.std-meta, in [structurally]). *)
and builtin_has (item : Hir.item) trait =
  match (item.home, item.name) with
  | "std.prelude", ("f32" | "f64") -> not (is_prelude trait "Hash")
  | "std.prelude", "Map" -> is_prelude trait "Eq" || is_prelude trait "Show"
  | "std.view", "Iter" | "std.lazy", "Lazy" -> false
  | _ -> true

let implements env bounds ty trait = implements_in env bounds [] ty trait

(* traits.structural-impls: a type constructor has a structural impl of a
   trait when its type would implement it with every type parameter
   implementing it. *)
let structural_impl env item trait =
  List.mem trait trait_bounds
  &&
  match type_info env item with
  | Some info ->
      let bounds =
        List.map (fun v -> (v, [ { trait; args = [] } ])) info.params
      in
      let ty = T.Con (item, List.map (fun v -> T.Param v) info.params) in
      implements env bounds ty trait = Yes
  | None -> false

let has_impl env ty trait =
  match T.resolve ty with
  | Con (item, _) ->
      Option.is_some (trait_impl env ~trait item)
      || structural_impl env item trait
  | Tuple _ | Record _ -> List.mem trait trait_bounds
  | Param _ | Spread _ | Fn _ | Forall _ | App _ | Handler _ | Var _ | Value _
  | Error ->
      false
