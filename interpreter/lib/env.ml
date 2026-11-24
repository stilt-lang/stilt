(* The environment of a program, built in three steps: the signatures of
   every module's items, then the impls, inherent ones first, and last the
   rules about declarations that need neither. *)

open Env_items
open Env_impls
open Env_checks
include Env_tables

let synthetic = Env_items.synthetic
let of_hir = Env_signatures.of_hir
let bounds_of = Env_signatures.bounds_of
let signature = Env_signatures.signature
let passing = Env_signatures.passing

type answer = Env_implements.answer = Yes | No | Unknown

let implements = Env_implements.implements
let has_impl = Env_implements.has_impl
let impl_subst = Env_implements.impl_subst
let trait_args = Env_implements.trait_args

let build (program : Hir.program) =
  let d = { list = [] } in
  let sites = impl_sites d program in
  (* Inherent impls first, so that each trait impl sees every inherent
     method of its type. *)
  let env, methods =
    List.fold_left
      (fun (env, methods) site ->
        match (site.head, site.node.desc.trait_) with
        | Broken owner, _ -> (add_broken env site owner, methods)
        | Head owner, Some { trait = Trait_error; _ } ->
            (add_broken env site (Some owner), methods)
        | Head owner, None ->
            let env, added = add_inherent d env site owner in
            (env, methods @ added)
        | Head _, Some { trait = Trait_ref _; _ } -> (env, methods))
      (declare_items program, [])
      sites
  in
  let env =
    List.fold_left
      (fun env site ->
        match (site.head, site.node.desc.trait_) with
        | Head owner, Some { trait = Trait_ref trait; args } ->
            add_trait_impl d env site owner trait args
        | (Head _ | Broken _), _ -> env)
      env sites
  in
  check_structural_clashes d env methods;
  check_record_cycles d env program;
  check_main d env program;
  check_wheres d env program;
  let std_errors, errors = List.partition fst d.list in
  if std_errors <> [] then
    failwith
      ("the standard library has errors: "
      ^ String.concat "; "
          (List.map (fun (_, e) -> Diagnostic.to_string e) std_errors));
  (env, List.map snd errors)
