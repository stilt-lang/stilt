(* generics.value-parameters-determined: a call gives a function's value parameter a value only
   through its parameters' types and its result type, outside every row, so
   one that appears in none is E0346. *)

open Hir
open Resolve_context
open Resolve_types

(* Whether [name] is written in [t] as a type of one name, outside every
   row and the type parameters of a polymorphic function type. *)
let rec written_in name (t : Ast.ty) =
  match t.desc with
  | Ty_named ([ n ], _) when n.desc = name -> true
  | Ty_named (_, ts) | Ty_tuple ts -> List.exists (written_in name) ts
  | Ty_record (fields, _) ->
      List.exists (fun (f : Ast.field_decl) -> written_in name f.ty) fields
  | Ty_spread t -> written_in name t
  | Ty_fn (_, ps, ret, _) ->
      List.exists (fun (_, t) -> written_in name t) ps
      || Option.fold ~none:false ~some:(written_in name) ret
  | Ty_handler (e, ret, _) ->
      let args =
        match e with Effect_named (_, ts) -> ts | Effect_async _ -> []
      in
      List.exists (written_in name) (args @ Option.to_list ret)
  | _ -> false

(* The types a call reads, each as written, if it is, and as resolved. *)
let typed (f : Ast.fn_decl) params ret =
  let params = List.combine f.params params in
  Option.fold ~none:[] ~some:(fun t -> [ (f.ret, t) ]) ret
  @ List.filter_map
      (function
        | Ast.Param (_, _, w, _), Param (_, _, t, _) -> Some (Some w, t)
        | _, Self_param (_, _, Some t) -> Some (None, t)
        | _ -> None)
      params

let check ctx generics f (params, ret) =
  let types = typed f params ret in
  (* A type that failed to resolve may hold the parameter where it is
     written, so no diagnostic arises from that type (errors.error-type, "The
     error type"). *)
  let stands (var : var) =
    List.exists
      (fun (w, t) ->
        mentions ~rows:false var t
        || (has_error t && Option.fold ~none:false ~some:(written_in var.name) w))
      types
  in
  (* One named as a generic before it is E0208, and no generic of its own. *)
  let named = List.map fst ctx.value_params @ List.map fst ctx.row_vars in
  ignore
    (List.fold_left
       (fun named -> function
         | Type_param { var; value = Some _; _ } when List.mem var.name named ->
             named
         (* A value parameter whose type is an error, or no integer type or
            [bool] (E0345), which was reported where it is written, stands
            nowhere as a value (errors.error-type). *)
         | Type_param { var; value = Some t; _ }
           when Option.is_none (Resolve_values.value_type t) ->
             var.name :: named
         | Type_param { var; value = Some _; _ } ->
             if not (stands var) then
               errorf ctx Code.e0346 var.loc
                 "`%s` appears in no parameter's type and not in the result \
                  type, so no call could say what it is"
                 var.name;
             var.name :: named
         | Row_param v -> v.name :: named
         | Type_param _ -> named)
       named generics)
