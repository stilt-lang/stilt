(* Members of types and traits: the methods found for a receiver, and members
   named as [Type.m] or [Trait.m] (traits.methods and traits.qualified-calls; traits.functions-without-self and traits.trait-constants). *)

module T = Types
module A = Tast
open Check_state
open Check_expect
open Check_types

type found =
  | Inherent of Env.member
  | Via_trait of Hir.item * Env.trait_method * Env.trait_info
  | Ambiguous of Hir.item list
  | Missing

type member_use =
  | Callable of
      A.callee * T.ty list * (T.mode * T.ty) list * T.ty * T.row * bool
  | Trait_constant of A.expr
  | Reflection of A.reflect * T.ty

let trait_methods st trait name =
  match Env.trait_info st.env trait with
  | Some info ->
      List.filter_map
        (fun (m : Env.trait_method) ->
          if m.method_name = name then Some (m, info) else None)
        info.methods
  | None -> []

(* The traits of the bounds of a type parameter, which a constructor
   parameter applied has too (traits.constructor-parameters). *)
let bounded st ty =
  match T.resolve ty with
  | Param p | App (Param p, _) ->
      Some
        (List.concat_map
           (fun ((v : Hir.var), bounds) ->
             if v.id = p.id then
               List.map (fun (b : Env.bound) -> b.trait) bounds
             else [])
           st.bounds)
  | _ -> None

(* traits.method-resolution *)
let find_method st ty name =
  let via traits =
    match
      List.concat_map
        (fun trait ->
          List.map
            (fun (m, info) -> (trait, m, info))
            (trait_methods st trait name))
        traits
    with
    | [] -> Missing
    | [ (trait, m, info) ] -> Via_trait (trait, m, info)
    | many -> Ambiguous (List.map (fun (trait, _, _) -> trait) many)
  in
  let implemented () =
    List.filter (fun trait -> Env.has_impl st.env ty trait) st.traits
  in
  match (T.resolve ty, bounded st ty) with
  | _, Some traits -> via traits
  | Con (item, _), None -> (
      match
        List.find_opt
          (fun (m : Env.member) -> m.name = name)
          (Env.inherent_members st.env item)
      with
      | Some m -> Inherent m
      | None -> via (implemented ()))
  | (Tuple _ | Record _ | Fn _), None -> via (implemented ())
  | ( ( Param _ | App _ | Spread _ | Forall _ | Handler _ | Var _ | Value _
      | Error ),
      None ) ->
      Missing

(* The type constructor at the head of a type. *)
let head ty = match T.resolve ty with Con (item, _) -> Some item | _ -> None

let unknown_in st name trait =
  match Env.trait_info st.env trait with
  | Some info -> List.mem name info.unknown_methods
  | None -> false

(* Whether a method that [ty] lacks is one that an error leaves out, whose
   uses have the error type (errors.error-type): a member of an impl with an
   error, or a method that a syntax error leaves without a signature, of an
   impl or of a trait that [ty] implements or is bounded by. *)
let left_out st ty name =
  (* A program's impls add no member to the library's types, so the library's own code never
     meets one that an error leaves out, whatever type a broken impl names. *)
  ((not st.module_.std) && Env.in_broken_impl st.env (head ty) name)
  ||
  let traits =
    match bounded st ty with
    | Some traits -> traits
    | None -> List.filter (fun trait -> Env.has_impl st.env ty trait) st.traits
  in
  List.exists (unknown_in st name) traits

let visible st (m : Env.member) = m.pub || m.owner.home = st.module_.name

(* program.visibility *)
let require_visible st (name : Hir.name) (m : Env.member) =
  if not (visible st m) then
    error st Code.e0213 name.loc "`%s` is private to module `%s`" name.desc
      m.owner.home

(* traits.method-resolution *)
let ambiguous st (name : Hir.name) traits =
  error st Code.e0319 name.loc
    "`%s` is a method of %s; call it as `Trait.%s(x, …)`" name.desc
    (String.concat " and "
       (List.map (fun (t : Hir.item) -> "`" ^ t.name ^ "`") traits))
    name.desc

(* traits.constructor-traits: what [Self] is for a value of type [ty]: the type, or for
   a constructor trait the constructor at its head. *)
let trait_self (info : Env.trait_info) ty =
  if info.arity = 0 then ty
  else
    match T.resolve ty with
    | App (h, _) -> h
    | Con (item, _) -> T.Con (item, [])
    | t -> t

(* traits.trait-arguments and traits.bound-arguments: the trait's parameters, as the impl or the bound of
   [self] gives them, which inference finds once [self] is known. *)
let trait_fixed st loc trait (info : Env.trait_info) self =
  let vars = List.map (fun v -> (v, fresh st loc)) info.params in
  fix st self trait (List.map snd vars) loc;
  vars

(* A function of [trait] named on the type [self], instantiated. *)
let instantiate_trait st loc ~use_at trait (m : Env.trait_method) info self =
  let fixed = trait_fixed st loc trait info self in
  instantiate ~fixed st loc m.method_sig
    ~self:(Some (info.self_param, self))
    ~use_at

(* A method of a trait, named as [Trait.m]. A function without [self] or a
   constant can't be named so: nothing gives the type whose impl is meant
   (traits.impl-members). *)
let trait_member st loc (trait : Hir.item) (name : Hir.name) =
  match trait_methods st trait name.desc with
  | (m, _) :: _ when m.member_kind = Function || m.member_kind = Constant ->
      error st Code.e0330 loc
        "`%s.%s` names no type, so nothing says which impl is meant; write the \
         type, as `T.%s`"
        trait.name name.desc name.desc;
      None
  | (m, info) :: _ ->
      let self = fresh st loc in
      obligation st self trait name.loc;
      let targs, params, ret, row =
        instantiate_trait st name.loc ~use_at:loc trait m info self
      in
      Some
        (Callable
           ( A.Trait_method (trait, m.method_name, self),
             targs,
             params,
             ret,
             row,
             m.method_sig.projection ))
  | [] ->
      if not (unknown_in st name.desc trait) then
        error st Code.e0314 name.loc "`%s` has no method `%s`" trait.name
          name.desc;
      None

let inherent_member st loc (hty : Hir.ty) resolved (name : Hir.name)
    (m : Env.member) =
  require_visible st name m;
  let targs, params, ret, row =
    instantiate st name.loc m.signature ~self:None ~use_at:loc
  in
  let impl_args =
    List.filteri (fun i _ -> i < List.length m.impl_generics) targs
  in
  let impl_self =
    T.subst
      (List.map2 (fun (v, _) t -> (v, t)) m.impl_generics impl_args)
      [] m.self_ty
  in
  expect st hty.loc ~expected:impl_self resolved;
  Callable
    (A.Member (m.owner, m.name), targs, params, ret, row, m.signature.projection)

(* A function or constant of a trait that [resolved] implements or is
   bounded by, named on it (traits.qualified-calls; traits.functions-without-self and traits.trait-constants). *)
let via_trait st loc resolved (name : Hir.name) trait (m : Env.trait_method)
    info =
  let self = trait_self info resolved in
  obligation st self trait name.loc;
  let targs, params, ret, row =
    instantiate_trait st name.loc ~use_at:loc trait m info self
  in
  match m.member_kind with
  | Constant ->
      (* traits.trait-constants: a trait constant has one value for each impl, so
         [List.MAX] leaves the type's arguments undecided. *)
      (match T.resolve resolved with
      | Con (_, args) ->
          List.iter
            (fun t ->
              match T.unsolved t with
              | Some info -> st.unknown <- info.id :: st.unknown
              | None -> ())
            args
      | _ -> ());
      Option.iter
        (fun owner ->
          match Env.trait_impl st.env ~trait owner with
          | Some impl
            when List.exists
                   (fun (mb : Env.member) -> mb.name = m.method_name)
                   impl.members ->
              st.constants <-
                Of_impl (trait, owner, m.method_name) :: st.constants
          | _ -> ())
        (head resolved);
      Trait_constant
        (node (A.Trait_constant (trait, m.method_name, self)) ret loc)
  | Method _ | Function ->
      Callable
        ( Trait_method (trait, m.method_name, self),
          targs,
          params,
          ret,
          row,
          m.method_sig.projection )

(* traits.shared-member-names and traits.functions-without-self: a function without [self] or a constant that two traits
   give a type is named through neither, since no form names it through one
   trait. A method is, as [Trait.m]. *)
let ambiguous_member st resolved (name : Hir.name) traits =
  let methods =
    List.for_all
      (fun trait ->
        List.for_all
          (fun ((m : Env.trait_method), _) ->
            match m.member_kind with Method _ -> true | _ -> false)
          (trait_methods st trait name.desc))
      traits
  in
  if methods then ambiguous st name traits
  else
    error st Code.e0319 name.loc
      "`%s` is a member of %s, so `%s.%s` could be either; rename it in one of \
       the traits"
      name.desc
      (String.concat " and "
         (List.map (fun (t : Hir.item) -> "`" ^ t.name ^ "`") traits))
      (show resolved) name.desc

(* A member of a type, named as [Type.m]. *)
let type_member st loc (hty : Hir.ty) (name : Hir.name) =
  let ty = named_type st hty in
  match T.resolve ty with
  | Error -> None
  | resolved -> (
      match find_method st resolved name.desc with
      | Inherent m -> Some (inherent_member st loc hty resolved name m)
      | Via_trait (trait, m, info) ->
          Some (via_trait st loc resolved name trait m info)
      | Ambiguous traits ->
          ambiguous_member st resolved name traits;
          None
      (* A member that an error leaves out is still the type's, found before
         the reflection of meta.shape-and-name (errors.broken-blocks). *)
      | Missing when left_out st resolved name.desc -> None
      | Missing -> (
          match Check_meta.reflection st resolved name with
          | Some (r, ty) -> Some (Reflection (r, ty))
          | None ->
              error st Code.e0314 name.loc "`%s` has no member `%s`"
                (show resolved) name.desc;
              None))

(* A member of a type or a trait, named as [Type.m] or [Trait.m] (traits.associated-functions and traits.qualified-calls), as a callee with its instantiated signature. *)
let member ctx loc (owner : Hir.owner) (name : Hir.name) =
  let st = ctx.st in
  match owner with
  | Of_trait trait -> trait_member st loc trait name
  | Of_type hty -> type_member st loc hty name

(* projections.call-is-place: a projection's call is a place, so its name is only
   called. *)
let projection_value st loc =
  error st Code.e0426 loc
    "a projection can only be called: its call is a place, so it has no \
     function type";
  error_node loc

let member_value ctx loc owner (name : Hir.name) =
  let st = ctx.st in
  match member ctx loc owner name with
  | None -> error_node loc
  | Some (Trait_constant e) -> e
  (* meta.shape-and-name: a function without parameters. *)
  | Some (Reflection (r, ty)) ->
      node
        (Closure ([], [], node (Reflect r) ty loc))
        (T.Fn ([], ty, T.empty_row))
        loc
  | Some (Callable (_, _, _, _, _, true)) -> projection_value st loc
  | Some (Callable (target, targs, params, ret, row, false)) -> (
      Check_foreign.used st loc target targs;
      match (target, owner) with
      | Member (item, n), Of_type _ -> (
          match
            List.find_opt
              (fun (m : Env.member) -> m.name = n)
              (Env.inherent_members st.env item)
          with
          | Some { kind = Constant; _ } ->
              (* declarations.constant-declarations: the constant is the same for every type
                 argument, so [Type.NAME] leaves them undecided. *)
              List.iter
                (fun t ->
                  match T.unsolved t with
                  | Some info -> st.unknown <- info.id :: st.unknown
                  | None -> ())
                targs;
              st.constants <- Assoc (item, n) :: st.constants;
              node (Member_constant (item, n, targs)) ret loc
          | _ -> node (Callee (target, targs)) (T.Fn (params, ret, row)) loc)
      | _ -> node (Callee (target, targs)) (T.Fn (params, ret, row)) loc)
