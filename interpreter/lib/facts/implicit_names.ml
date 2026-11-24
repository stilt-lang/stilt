(* The items that operations name (facts.inference). *)

module T = Types

type key =
  | Function of Hir.item
  | Member of Hir.item * string
  | Impl_method of Hir.item * Hir.item * string
  | Default_method of Hir.item * string
  | Built_in of Hir.item * string

let show_key = function
  | Function item -> item.name
  | Member (owner, name) | Impl_method (_, owner, name) ->
      owner.name ^ "." ^ name
  | Default_method (trait, name) | Built_in (trait, name) ->
      trait.name ^ "." ^ name

let subst (info : Env.type_info) args t =
  if List.length info.params = List.length args then
    T.subst (List.combine info.params args) [] t
  else T.Error

let prelude = T.prelude_item

let trait_methods env trait =
  match Env.trait_info env trait with
  | Some info ->
      List.map (fun (m : Env.trait_method) -> m.method_name) info.methods
  | None -> []

let writes (impl : Env.impl) name =
  List.exists (fun (m : Env.member) -> m.name = name) impl.members

(* traits.structural-calls and traits.show: the method a structural impl calls on each
   component. Containers show their elements with [show_nested]. *)
let component trait name =
  if trait = prelude "Show" then "show_nested" else name

(* The types a structural impl reaches into. *)
let held env item args =
  match Env.type_info env item with
  | Some ({ def = Record fields; _ } as info) ->
      List.map (fun (_, t) -> subst info args t) fields
  | Some ({ def = Variants vs; _ } as info) ->
      List.concat_map (fun (_, p) -> List.map (subst info args) p) vs
  | Some { def = Builtin; _ } -> args
  | None -> []

(* facts.inference, trait methods: the items that calling the method [name] of
   [trait] on a value of type [ty] names. That is the impl's method, or the
   trait's default method together with the impl's other methods, which the
   default calls through [Self]; and the impl methods that the impl's bounds
   require of the type's arguments. An impl that no source declares names its
   own method, and what it calls on each component. A type parameter names
   nothing, since a call through a bound is a call through a function value
   (facts.calls-through-function-values). *)
(* The methods that calling [name] through [impl] of [trait] for [item] runs:
   the impl's own, or the trait's default followed by every other method of
   the trait. *)
let impl_names env (impl : Env.impl) trait item name =
  let own n =
    if writes impl n then Impl_method (trait, item, n)
    else Default_method (trait, n)
  in
  if writes impl name then [ own name ]
  else List.map own (name :: List.filter (( <> ) name) (trait_methods env trait))

let rec method_names env visiting trait name ty =
  match T.resolve ty with
  | Param _ | Var _ | Error | Fn _ | Forall _ | App _ | Spread _ | Handler _
  | Value _ ->
      []
  | Record fields ->
      Built_in (trait, name)
      :: List.concat_map
           (method_names env visiting trait (component trait name))
           (List.map snd fields)
  | Tuple ts ->
      Built_in (trait, name)
      :: List.concat_map
           (method_names env visiting trait (component trait name))
           ts
  | Con (item, args) -> (
      match Env.trait_impl env ~trait item with
      | Some impl ->
          impl_names env impl trait item name
          @ generic_names env visiting impl args
      | None when List.mem (item, trait) visiting -> []
      | None ->
          let visiting = (item, trait) :: visiting in
          Built_in (trait, name)
          :: List.concat_map
               (method_names env visiting trait (component trait name))
               (held env item args))

(* Every method of the impl of [trait] for [ty]: what a bound requires. An
   impl's own bounds are required once for all its methods, which keeps a type
   nested through impls with bounds linear in its depth. *)
and bound_names env visiting trait ty =
  let methods = trait_methods env trait in
  match T.resolve ty with
  | Con (item, args) when Option.is_some (Env.trait_impl env ~trait item) ->
      let impl = Option.get (Env.trait_impl env ~trait item) in
      List.concat_map (impl_names env impl trait item) methods
      @ generic_names env visiting impl args
  | _ ->
      List.concat_map
        (fun name -> method_names env visiting trait name ty)
        methods

and generic_names env visiting (impl : Env.impl) args =
  let params = match impl.self_ty with Con (_, ps) -> ps | _ -> [] in
  if List.length params <> List.length args then []
  else
    List.concat_map
      (fun (param, arg) ->
        match param with
        | T.Param v ->
            List.concat_map
              (fun ((w : Hir.var), traits) ->
                if w.id = v.id then
                  List.concat_map
                    (fun (b : Env.bound) ->
                      bound_names env visiting b.trait arg)
                    traits
                else [])
              impl.generics
        | _ -> [])
      (List.combine params args)

let method_names env trait name ty = method_names env [] trait name ty

(* facts.inference: instantiating a generic function names the impl methods that its
   bounds require of its type arguments, which are the last of [targs]. *)
let instantiation_names env (s : Env.fn_sig option) targs =
  match s with
  | None -> []
  | Some s ->
      let n = List.length s.type_params and m = List.length targs in
      if m < n then []
      else
        List.concat
          (List.map2
             (fun (_, traits) arg ->
               List.concat_map
                 (fun (b : Env.bound) -> bound_names env [] b.trait arg)
                 traits)
             s.type_params
             (List.filteri (fun i _ -> i >= m - n) targs))

let member_sig env owner name =
  List.find_map
    (fun (m : Env.member) -> if m.name = name then Some m.signature else None)
    (Env.inherent_members env owner)

let trait_method_sig env trait name =
  Option.bind (Env.trait_info env trait) (fun info ->
      List.find_map
        (fun (m : Env.trait_method) ->
          if m.method_name = name then Some m.method_sig else None)
        info.methods)

let callee_names env (c : Tast.callee) targs =
  match c with
  | Function item ->
      Function item :: instantiation_names env (Env.function_sig env item) targs
  | Member (owner, name) ->
      Member (owner, name)
      :: instantiation_names env (member_sig env owner name) targs
  | Trait_method (trait, name, ty) ->
      method_names env trait name ty
      @ instantiation_names env (trait_method_sig env trait name) targs
  (* handlers.implicit-effects-and-capabilities: a performance is a call through a stored function
     value, which names nothing. *)
  | Operation _ -> []

(* The item a call by name calls, which is the first that it names. *)
let callee_key env (c : Tast.callee) =
  match c with
  | Function item -> Some (Function item)
  | Member (owner, name) -> Some (Member (owner, name))
  | Trait_method (trait, name, ty) -> (
      match T.resolve ty with
      | Con (item, _) -> (
          match Env.trait_impl env ~trait item with
          | Some impl when writes impl name ->
              Some (Impl_method (trait, item, name))
          | Some _ -> Some (Default_method (trait, name))
          | None -> Some (Built_in (trait, name)))
      | Tuple _ | Record _ -> Some (Built_in (trait, name))
      | Param _ | Var _ | Error | Fn _ | Forall _ | App _ | Spread _ | Handler _
      | Value _ ->
          None)
  | Operation _ -> None

(* std.finding-keys *)
let key_names env ty =
  match T.resolve ty with
  | Con (_, [ key; _ ]) ->
      bound_names env [] (prelude "Eq") key
      @ bound_names env [] (prelude "Hash") key
  | _ -> []

let signature env = function
  | Function item -> Env.function_sig env item
  | Member (owner, name) -> member_sig env owner name
  | Built_in (trait, name) -> trait_method_sig env trait name
  | Impl_method _ | Default_method _ -> None
