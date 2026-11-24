(* Impls and the rules they follow (traits.impl-blocks, traits.implementing-trait and traits.impl-members): where they are
   written, their types and their members. *)

module T = Types
open Env_tables
open Env_signatures
open Env_implements
open Env_items

type impl_site = {
  site_module : Hir.module_;
  node : Hir.impl_decl Hir.node;
  generics : bounds;
  head : head;
}

and head = Head of Hir.item | Broken of Hir.item option

(* traits.impl-blocks and traits.implementing-trait: an impl's type is a type constructor applied to the
   impl's type parameters, each once, but for those that its member types
   imply (traits.member-types). *)
let impl_head d (m : Hir.module_) (i : Hir.impl_decl) =
  let invalid owner =
    report d m Code.e0302 i.self_ty.loc
      "an impl's type must be a type applied to the impl's own type \
       parameters, each once";
    Broken owner
  in
  match i.self_ty.desc with
  | Ty_error -> Broken None
  | Ty_con (item, args)
    when List.exists (fun (a : Hir.ty) -> a.desc = Ty_error) args ->
      Broken (Some item)
  | Ty_con (item, args) ->
      let params =
        List.filter_map
          (fun (a : Hir.ty) ->
            match a.desc with Ty_param v -> Some v.id | _ -> None)
          args
      in
      let generic_ids =
        List.filter_map
          (fun (p : Hir.type_param) ->
            if p.implied then None else Some p.var.id)
          i.generics
      in
      if
        List.length params = List.length args
        && List.length params = List.length generic_ids
        && List.sort_uniq compare params = List.sort compare generic_ids
      then Head item
      else invalid (Some item)
  | Ty_param _ | Ty_self | Ty_tuple _ | Ty_record _ | Ty_spread _ | Ty_fn _
  | Ty_app _ | Ty_self_app _ | Ty_handler _ | Ty_value _ ->
      invalid None

(* Every impl of the program, in the order of the program. *)
let impl_sites d (program : Hir.program) =
  List.concat_map
    (fun (m : Hir.module_) -> List.map (fun node -> (m, node)) m.impls)
    program
  |> List.stable_sort
       (fun ((m : Hir.module_), (i : Hir.impl_decl Hir.node)) (n, j) ->
         compare
           (m.file, i.loc.line, i.loc.col)
           (n.Hir.file, j.loc.line, j.loc.col))
  |> List.map (fun ((m : Hir.module_), (node : Hir.impl_decl Hir.node)) ->
      let generics = bounds_of node.desc.generics in
      { site_module = m; node; generics; head = impl_head d m node.desc })

(* The members of an impl for the type constructor [owner], each with the
   position of its name. *)
let impl_members env site ~owner ~trait_ =
  let self_ty = of_hir site.node.desc.self_ty in
  let type_pub =
    Option.fold ~none:false
      ~some:(fun (info : type_info) -> info.pub)
      (type_info env owner)
  in
  List.map
    (fun (member : Hir.decl Hir.node) ->
      let name = decl_name member in
      let kind, signature =
        match member.desc.kind with
        | Fn f ->
            ( (match f.params with
              | Self_param (mode, _, _) :: _ -> Method mode
              | _ -> Function),
              signature ~self_ty ~outer:site.generics f )
        | Const c ->
            ( Constant,
              {
                type_params = site.generics;
                row_params = [];
                assumed = [];
                params = [];
                ret = of_hir c.ty;
                projection = false;
                row = T.empty_row;
              } )
        | Type _ | Trait _ | Test _ | Effect _ -> invalid_arg "Env.impl_members"
      in
      ( {
          name = name.desc;
          pub = Option.is_some trait_ || (member.desc.pub && type_pub);
          kind;
          signature;
          owner;
          impl_generics = site.generics;
          self_ty;
        },
        name.loc ))
    (List.filter
       (fun (member : Hir.decl Hir.node) -> not member.desc.unknown)
       site.node.desc.members)

(* The members of an impl that a syntax error leaves without a signature,
   whose uses have the error type (errors.broken-parts), each with the place of its
   name. *)
let unknown_places site =
  List.filter_map
    (fun (member : Hir.decl Hir.node) ->
      if member.desc.unknown then
        let name = decl_name member in
        Some (name.desc, name.loc)
      else None)
    site.node.desc.members

let unknown_members site = List.map fst (unknown_places site)

let add_unknown env site owner =
  {
    env with
    broken =
      List.map (fun name -> (Some owner, name)) (unknown_members site)
      @ env.broken;
  }

(* Records the members of an impl with an error, whose uses have the error
   type (errors.declarations-with-errors). *)
let add_broken env site owner =
  let names =
    List.map
      (fun member -> (owner, (decl_name member).desc))
      site.node.desc.members
  in
  { env with broken = names @ env.broken }

(* Adds an inherent impl, and returns its members with their modules and
   positions. An impl outside the type's home module adds no member, so it
   changes no other module (traits.impl-blocks). *)
let add_inherent d env site (owner : Hir.item) =
  let m = site.site_module in
  if owner.home <> m.name then (
    report d m Code.e0301 site.node.desc.self_ty.loc
      "only the home module of `%s`, `%s`, may hold its impl blocks" owner.name
      owner.home;
    (add_broken env site (Some owner), []))
  else
    let env = add_unknown env site owner in
    let members = impl_members env site ~owner ~trait_:None in
    let inherent =
      Imap.update owner
        (fun ms -> Some (Option.value ms ~default:[] @ List.map fst members))
        env.inherent
    in
    ({ env with inherent }, List.map (fun (mb, loc) -> (mb, m, loc)) members)

let methods_of env trait =
  Option.fold ~none:[] ~some:(fun info -> info.methods) (trait_info env trait)

let describe_kind = function
  | Method _ -> "method"
  | Function -> "function"
  | Constant -> "constant"

(* Whether an impl's member [mb] has the trait's signature [tm], once [Self]
   is the impl's type and each trait parameter the impl's argument (traits.impl-signatures; traits.trait-arguments and traits.functions-without-self). *)
let matches site (info : trait_info) (impl : impl) (tm : trait_method)
    (mb : member) =
  let fixed =
    if List.length info.params = List.length impl.trait_args then
      List.combine info.params impl.trait_args
    else []
  in
  match (tm.member_kind, mb.kind) with
  | Constant, Constant ->
      equal
        (T.subst
           ((info.self_param, impl.self_ty) :: fixed)
           [] tm.method_sig.ret)
        mb.signature.ret
  | Constant, _ | _, Constant -> false
  | _ ->
      matches_trait ~self_param:info.self_param ~self_ty:impl.self_ty ~fixed
        tm.method_sig mb.signature
        ~own:(List.length site.generics)

(* traits.impl-members, and traits.functions-without-self and traits.trait-constants: an impl holds each function and
   constant of the trait without a default, and no other member, each with
   the signature the trait declares. *)
let check_trait_methods d env site (impl : impl) ~(trait : Hir.item)
    ~(owner : Hir.item) members =
  let m = site.site_module in
  Option.iter
    (fun info ->
      List.iter
        (fun (tm : trait_method) ->
          if
            (not tm.has_default)
            && (not
                  (List.exists
                     (fun ((mb : member), _) -> mb.name = tm.method_name)
                     members))
            && not (List.mem tm.method_name (unknown_members site))
          then
            report d m Code.e0305 site.node.loc
              "the impl of `%s` for `%s` lacks the %s `%s`" trait.name
              owner.name
              (describe_kind tm.member_kind)
              tm.method_name)
        info.methods;
      List.iter
        (fun ((mb : member), loc) ->
          match
            List.find_opt
              (fun (tm : trait_method) -> tm.method_name = mb.name)
              info.methods
          with
          | None when List.mem mb.name info.unknown_methods -> ()
          | None ->
              report d m Code.e0306 loc "`%s` is not a member of `%s`" mb.name
                trait.name
          | Some tm ->
              if not (matches site info impl tm mb) then
                report d m Code.e0307 loc
                  "`%s` must have the signature that `%s` declares" mb.name
                  trait.name)
        members)
    (trait_info env trait)

(* Adds a trait impl, after every inherent impl. *)
let add_trait_impl d env site (owner : Hir.item) (trait : Hir.item) args =
  let m = site.site_module in
  match trait_impl env ~trait owner with
  (* traits.orphan-rule. An orphan impl adds nothing, so it changes no other
     module. *)
  | _ when trait.home <> m.name && owner.home <> m.name ->
      report d m Code.e0303 site.node.loc
        "an impl of `%s` for `%s` must be in module `%s` or `%s`" trait.name
        owner.name trait.home owner.home;
      add_broken env site (Some owner)
  | Some _ ->
      report d m Code.e0304 site.node.loc "`%s` already has an impl of `%s`"
        owner.name trait.name;
      env
  | None ->
      let env = add_unknown env site owner in
      let members = impl_members env site ~owner ~trait_:(Some trait) in
      let impl =
        {
          module_ = m.name;
          generics = site.generics;
          trait_ = Some trait;
          trait_args = List.map of_hir args;
          self_ty = of_hir site.node.desc.self_ty;
          loc = site.node.loc;
          members = List.map fst members;
          unknown = unknown_places site;
        }
      in
      check_trait_methods d env site impl ~trait ~owner members;
      (* traits.method-resolution *)
      List.iter
        (fun (mb : member) ->
          if
            List.exists
              (fun tm -> tm.method_name = mb.name)
              (methods_of env trait)
          then
            report d m Code.e0308 site.node.loc
              "`%s` has an inherent member `%s`, which this impl of `%s` would \
               hide"
              owner.name mb.name trait.name)
        (inherent_members env owner);
      { env with trait_impls = Pmap.add (trait, owner) impl env.trait_impls }

(* traits.name-clashes: an inherent method doesn't share a name with a method of a
   structural impl its type has, at the inherent method. *)
let check_structural_clashes d env methods =
  List.iter
    (fun ((mb : member), m, loc) ->
      List.iter
        (fun trait ->
          if
            List.exists
              (fun tm -> tm.method_name = mb.name)
              (methods_of env trait)
            && Option.is_none (trait_impl env ~trait mb.owner)
            && structural_impl env mb.owner trait
          then
            report d m Code.e0308 loc
              "`%s` implements `%s`, whose method `%s` this method would hide"
              mb.owner.name trait.name mb.name)
        trait_bounds)
    methods
