(* The program's traits, impls and functions as it writes them, as kinds read them, and the
   uses of its functions with constructor parameters (formal/Stilt/Syntax/Kinds.lean): the
   model checks their kinds (traits.constructor-traits, traits.receiver-types,
   traits.constructor-impls and traits.constructor-parameters) and runs the instances. Only the
   program's own modules are written: no trait of the standard library is over constructors. *)

open Model_json
open Model_types

let self = "Self"

(* A type as kinds read it, each generic that [names] numbers named by its position, the
   others by their names, and a [Self<…>] that [ctor] replaces, in the default of a trait that an
   impl leaves out, as [Con<…>]. Each named constructor met goes into [arities]. *)
let rec kty env arities names ctor (t : Hir.ty) =
  let go = kty env arities names ctor in
  let other ts = tag "other" [ Arr (List.map go ts) ] in
  let named (v : Hir.var) =
    match List.assoc_opt v.id names with Some k -> "#" ^ k | None -> v.name
  in
  match t.desc with
  | Ty_con (i, args) ->
      let n =
        match Env.type_info env i with
        | Some info -> List.length info.params
        | None -> List.length args
      in
      arities := (item_name i, n) :: !arities;
      tag "con" [ Str (item_name i); Arr (List.map go args) ]
  | Ty_param v -> tag "param" [ Str (named v); Arr [] ]
  | Ty_app (v, args) -> tag "param" [ Str (named v); Arr (List.map go args) ]
  | Ty_self -> tag "param" [ Str self; Arr [] ]
  | Ty_self_app args -> (
      match ctor with
      | Some c -> tag "con" [ Str c; Arr (List.map go args) ]
      | None -> tag "param" [ Str self; Arr (List.map go args) ])
  | Ty_tuple ts -> other ts
  | Ty_record fields ->
      other (List.map (fun (f : Hir.field_decl) -> f.ty) fields)
  | Ty_spread (_, t) -> other [ t ]
  (* A polymorphic function type's parameters are a calculus of their own. *)
  | Ty_fn (_ :: _, _, _, _) -> other []
  | Ty_fn ([], ps, r, _) -> other (List.map snd ps @ Option.to_list r)
  | Ty_handler (_, r, _) -> other (Option.to_list r)
  | Ty_value _ | Ty_error -> other []

let trait_name = function Hir.Trait_ref i -> item_name i | Trait_error -> "?"

(* A generic's name and the traits of its bounds. *)
let generic names (p : Hir.type_param) =
  let n =
    match List.assoc_opt p.var.id names with
    | Some k -> "#" ^ k
    | None -> p.var.name
  in
  Arr
    [
      Str n;
      Arr (List.map (fun (b : Hir.bound) -> Str (trait_name b.trait)) p.bounds);
    ]

let type_params (d : Hir.fn_decl) =
  List.filter_map
    (function Hir.Type_param p -> Some p | Row_param _ -> None)
    d.generics

(* A signature: [name, generics, receiver, params, result]. *)
let sig_ env arities ?ctor name (d : Hir.fn_decl) =
  let ps = type_params d in
  let names =
    List.mapi (fun k (p : Hir.type_param) -> (p.var.id, string_of_int k)) ps
  in
  let ty = kty env arities names ctor in
  let receiver =
    match d.params with
    | Self_param (_, _, None) :: _ -> Str "bare"
    | Self_param (_, _, Some t) :: _ -> tag "typed" [ ty t ]
    | _ -> Str "none"
  in
  let params =
    List.filter_map
      (function Hir.Param (_, _, t, _) -> Some (ty t) | Self_param _ -> None)
      d.params
  in
  let result =
    match d.ret with Some t -> ty t | None -> tag "other" [ Arr [] ]
  in
  Arr
    [
      Str name; Arr (List.map (generic names) ps); receiver; Arr params; result;
    ]

let fns (decls : Hir.decl Hir.node list) =
  List.filter_map
    (fun (d : Hir.decl Hir.node) ->
      match d.desc.kind with Fn f -> Some f | _ -> None)
    decls

let item (m : Hir.module_) (n : Hir.name) = { Hir.home = m.name; name = n.desc }

let traits (m : Hir.module_) =
  List.filter_map
    (fun (d : Hir.decl Hir.node) ->
      match d.desc.kind with Trait t -> Some (item m t.name, t) | _ -> None)
    m.decls

(* An impl: [trait, type, generics, members], with the defaults of a trait over constructors
   that it leaves out, written at its constructor. *)
let impl env arities all_traits (i : Hir.impl_decl) =
  let trait_ =
    match i.trait_ with Some b -> Some (trait_name b.trait) | None -> None
  in
  let own = List.map (fun (f : Hir.fn_decl) -> f.name.desc) (fns i.members) in
  let members =
    List.map
      (fun (f : Hir.fn_decl) -> sig_ env arities f.name.desc f)
      (fns i.members)
  in
  let defaults =
    match (trait_, i.self_ty.desc) with
    | Some t, Ty_con (c, []) -> (
        match List.assoc_opt t all_traits with
        | Some (tr : Hir.trait_decl) when tr.arity > 0 ->
            List.filter_map
              (fun (f : Hir.fn_decl) ->
                if f.body <> None && not (List.mem f.name.desc own) then
                  Some (sig_ env arities ~ctor:(item_name c) f.name.desc f)
                else None)
              (fns tr.members)
        | _ -> [])
    | _ -> []
  in
  Arr
    [
      (match trait_ with Some t -> Str t | None -> Null);
      kty env arities [] None i.self_ty;
      Arr (List.map (generic []) i.generics);
      Arr (members @ defaults);
    ]

(* The constructor each constructor parameter of a function's instance takes, by the
   parameter's position. *)
let use_of env user_fns (inst : fn_instance) =
  match inst.target with
  | Function i -> (
      match List.assoc_opt i user_fns with
      | Some (d : Hir.fn_decl) ->
          let ctors =
            List.concat
              (List.mapi
                 (fun k (p : Hir.type_param) ->
                   let over_ctors (b : Hir.bound) =
                     match b.trait with
                     | Trait_ref t -> (
                         match Env.trait_info env t with
                         | Some info -> info.arity > 0
                         | None -> false)
                     | Trait_error -> false
                   in
                   if List.exists over_ctors p.bounds then
                     let c =
                       match
                         List.find_opt
                           (fun ((v : Hir.var), _) -> v.id = p.var.id)
                           inst.types_of
                       with
                       | Some (_, t) -> (
                           match norm t with
                           | Con (c, []) -> item_name c
                           | _ -> "?")
                       | None -> "?"
                     in
                     [ Arr [ Str ("#" ^ string_of_int k); Str c ] ]
                   else [])
                 (type_params d))
          in
          if ctors = [] then None
          else Some (Arr [ Str (item_name i); Arr ctors ])
      | None -> None)
  | _ -> None

let written env (hir : Hir.program) (fns_reached : fn_instance list) =
  let mods = List.filter (fun (m : Hir.module_) -> not m.std) hir in
  let arities = ref [] in
  let all_traits =
    List.concat_map
      (fun m -> List.map (fun (i, t) -> (item_name i, t)) (traits m))
      mods
  in
  let trait_ (name, (t : Hir.trait_decl)) =
    Arr
      [
        Str name;
        Str (string_of_int t.arity);
        Arr (List.map (fun (v : Hir.var) -> Str v.name) t.params);
        Arr
          (List.map
             (fun (f : Hir.fn_decl) -> sig_ env arities f.name.desc f)
             (fns t.members));
      ]
  in
  let user_fns =
    List.concat_map
      (fun (m : Hir.module_) ->
        List.map (fun (f : Hir.fn_decl) -> (item m f.name, f)) (fns m.decls))
      mods
  in
  let traits_ = List.map trait_ all_traits in
  let impls =
    List.concat_map
      (fun (m : Hir.module_) ->
        List.map
          (fun (i : Hir.impl_decl Hir.node) ->
            impl env arities all_traits i.desc)
          m.impls)
      mods
  in
  let functions =
    List.map (fun (i, f) -> sig_ env arities (item_name i) f) user_fns
  in
  let uses = List.filter_map (use_of env user_fns) fns_reached in
  let arities =
    List.sort_uniq compare !arities
    |> List.map (fun (c, n) -> Arr [ Str c; Str (string_of_int n) ])
  in
  Obj
    [
      ("arities", Arr arities);
      ("traits", Arr traits_);
      ("impls", Arr impls);
      ("functions", Arr functions);
      ("uses", Arr uses);
    ]
