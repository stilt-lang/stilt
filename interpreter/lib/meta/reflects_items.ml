(* The items that may reflect (meta.reflects): their type parameters, and
   what each call or name of one gives them. *)

module T = Types
module K = Implicit_names

let member_sig env owner name =
  List.find_map
    (fun (m : Env.member) -> if m.name = name then Some m.signature else None)
    (Env.inherent_members env owner)

let trait_method env trait name =
  Option.bind (Env.trait_info env trait) (fun info ->
      List.find_map
        (fun (m : Env.trait_method) ->
          if m.method_name = name then Some (info, m) else None)
        info.methods)

let impl_member env trait owner name =
  Option.bind (Env.trait_impl env ~trait owner) (fun impl ->
      Option.map
        (fun m -> (impl, m))
        (List.find_opt (fun (m : Env.member) -> m.name = name) impl.members))

let drop n xs = List.filteri (fun i _ -> i >= n) xs
let vars (bounds : Env.bounds) = List.map fst bounds

(* The type parameters of an item, with their bounds, and those whose
   instantiation its callers can't see: a trait method's own, and a trait's
   [Self] in its default methods (meta.unseen-instantiations). *)
let params env (key : K.key) : Env.bounds * Hir.var list =
  match key with
  | Function item -> (
      match Env.function_sig env item with
      | Some s -> (s.type_params, [])
      | None -> ([], []))
  | Member (owner, name) -> (
      match member_sig env owner name with
      | Some s -> (s.type_params, [])
      | None -> ([], []))
  | Impl_method (trait, owner, name) -> (
      match impl_member env trait owner name with
      | Some (impl, m) ->
          ( m.signature.type_params,
            vars (drop (List.length impl.generics) m.signature.type_params) )
      | None -> ([], []))
  | Default_method (trait, name) -> (
      match trait_method env trait name with
      | Some (info, m) ->
          let args = List.map (fun v -> T.Param v) info.params in
          ( (info.self_param, [ { Env.trait; args } ])
            :: m.method_sig.type_params,
            info.self_param :: vars m.method_sig.type_params )
      | None -> ([], []))
  | Built_in _ -> ([], [])

let combine (bounds : Env.bounds) targs =
  let rec go bs ts =
    match (bs, ts) with (v, _) :: bs, t :: ts -> (v, t) :: go bs ts | _ -> []
  in
  go bounds targs

(* What calling or naming [callee] with [targs] gives the type parameters of
   the item it reaches, when it reaches one: a method called through a bound
   reaches none here. *)
let target env (callee : Tast.callee) targs =
  match callee with
  | Function _ | Member _ ->
      Option.map
        (fun key -> (key, combine (fst (params env key)) targs))
        (K.callee_key env callee)
  | Trait_method (trait, name, ty) -> (
      match K.callee_key env callee with
      | Some (Impl_method (_, owner, _) as key) -> (
          match (impl_member env trait owner name, T.resolve ty) with
          | Some (impl, m), Con (_, args) ->
              let own =
                drop (List.length impl.generics) m.signature.type_params
              in
              Some (key, Env.impl_subst env [] impl args @ combine own targs)
          | _ -> None)
      | Some (Default_method _ as key) ->
          let bounds, _ = params env key in
          Some (key, combine bounds (ty :: targs))
      | _ -> None)
  | Operation _ -> None

(* meta.types-without-shape: the impls that a type meets the bounds [bounds] with,
   each with its methods and what the type gives the impl's own type
   parameters, which are checked where the bound is met. *)
let met env (bounds : Env.bound list) ty =
  match T.resolve ty with
  | Con (owner, args) ->
      List.concat_map
        (fun (b : Env.bound) ->
          match Env.trait_impl env ~trait:b.trait owner with
          | Some impl ->
              let sub = Env.impl_subst env [] impl args in
              List.map
                (fun (m : Env.member) ->
                  (K.Impl_method (b.trait, owner, m.name), sub))
                impl.members
          | None -> [])
        bounds
  | _ -> []

let name (key : K.key) =
  match key with
  | Function item -> item.name
  | Member (owner, name) -> owner.name ^ "." ^ name
  | Impl_method (_, owner, name) -> owner.name ^ "." ^ name
  | Default_method (trait, name) | Built_in (trait, name) ->
      trait.name ^ "." ^ name
