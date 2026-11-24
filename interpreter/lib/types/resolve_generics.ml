(* The generics that declare type parameters and row variables, their bounds,
   and [where] clauses (effects.row-variables; traits.bounded-blocks; traits.bound-arguments, traits.member-types and traits.where
   and 9). *)

open Hir
open Resolve_context
open Resolve_types

(* Declares a type parameter or row variable [n] in [scope]. Of two with the
   same name, the first stays declared, and a function's generics can't reuse
   the names of its impl block's (traits.impl-blocks), nor a trait function's
   those of its trait's parameters (traits.trait-parameters). *)
let declare ctx scope what (n : name) =
  let v = fresh ctx n in
  if List.mem_assoc n.desc scope then (
    errorf ctx Code.e0208 n.loc "`%s` is already %s here" n.desc what;
    (v, scope))
  else (v, (n.desc, v) :: scope)

(* traits.constructor-parameters: the arity of a type parameter that a constructor trait
   bounds, which only a function's generics are, and which no other trait
   bounds beside it. *)
let kind_of ctx ~impl resolved =
  let known = List.filter (fun r -> r.bound.trait <> Trait_error) resolved in
  match List.find_opt (fun r -> r.arity > 0) known with
  | None -> None
  | Some first when impl ->
      errorf ctx Code.e0337 first.at
        "a trait over type constructors bounds only a function's generics";
      None
  | Some first ->
      (match List.find_opt (fun r -> r.arity <> first.arity) known with
      | Some other ->
          errorf ctx Code.e0337 other.at
            "this bound is over %s, and an earlier one over constructors of %d \
             argument%s, so no type meets both"
            (if other.arity = 0 then "types"
             else Printf.sprintf "constructors of %d" other.arity)
            first.arity (plural first.arity)
      | None -> ());
      Some first.arity

(* The traits of a type parameter's bounds, with their parameters and the
   arguments that give them, which its member types name (traits.member-types). *)
let members_of resolved =
  List.filter_map
    (fun r ->
      match r.bound.trait with
      | Trait_ref item when r.params <> [] ->
          Some (item, List.combine r.params r.bound.args)
      | Trait_ref _ | Trait_error -> None)
    resolved

(* A list of bounds, as its trait bounds and the types of its record bounds
   (records.record-bounds). *)
let split_bounds (bounds : Ast.bound list) =
  List.partition_map
    (function
      | Ast.Trait_bound _ as b -> Either.Left b
      | Record_bound t -> Either.Right t)
    bounds

(* Resolves the bounds of the type parameters [declared], once all of them
   are in scope, so that a bound's argument may be another one (traits.bound-arguments). Returns the context with their kinds and member types, the type
   parameters, and those that their member types imply. *)
let bound_params ctx ~impl declared =
  let resolved =
    List.map
      (fun ((p : Ast.type_param), (v : var)) ->
        let traits, _ = split_bounds p.bounds in
        (v, List.map (resolve_bound ctx ~implied_by:v.name) traits))
      declared
  in
  let kinds =
    List.filter_map
      (fun ((v : var), rs) ->
        Option.map (fun k -> (v.id, k)) (kind_of ctx ~impl rs))
      resolved
  in
  let members =
    List.map (fun ((v : var), rs) -> (v.id, members_of rs)) resolved
  in
  let params =
    List.map2
      (fun ((p : Ast.type_param), _) (var, rs) ->
        let _, records = split_bounds p.bounds in
        {
          var;
          bounds = List.map (fun r -> r.bound) rs;
          fields = List.concat_map (record_bound ctx) records;
          pack = p.pack;
          implied = false;
          value = None;
        })
      declared resolved
  in
  let implied =
    List.concat_map
      (fun (_, rs) -> List.concat_map (fun r -> r.implied) rs)
      resolved
  in
  ( { ctx with kinds = kinds @ ctx.kinds; members = members @ ctx.members },
    params,
    implied )

(* generics.value-parameters: a value parameter, a type parameter of [ctx]'s list
   whose [value] is its type. *)
let declare_value ctx (n : name) (t : Ast.ty) =
  let t = resolve_ty ctx t in
  let ctx, var = Resolve_values.declare ctx n t in
  let param =
    {
      var;
      bounds = [];
      fields = [];
      pack = false;
      implied = false;
      value = Some t;
    }
  in
  (ctx, param)

(* What a list of generics declares, in order: a type parameter, whose
   bounds are resolved once every one is in scope, a value parameter or a
   row variable. *)
type declared = Type_var of var | Value_var of type_param | Row_var of var

let declare_param (ctx, declared, order) (p : Ast.type_param) =
  match p.value with
  | Some t ->
      let ctx, param = declare_value ctx p.name t in
      (ctx, declared, order @ [ Value_var param ])
  | None ->
      let v, type_params =
        declare ctx ctx.type_params "a type parameter" p.name
      in
      ({ ctx with type_params }, declared @ [ (p, v) ], order @ [ Type_var v ])

(* The generics of [order], with the type parameters that [params] gives. *)
let in_order params order =
  List.map
    (function
      | Type_var (v : var) ->
          Type_param (List.find (fun p -> p.var.id = v.id) params)
      | Value_var p -> Type_param p
      | Row_var v -> Row_param v)
    order

(* An impl's type parameters and value parameters, those that member types
   imply last. *)
let declare_impl_generics ctx (params : Ast.type_param list) =
  let ctx, declared, order =
    List.fold_left declare_param (ctx, [], []) params
  in
  let ctx, params, implied = bound_params ctx ~impl:true declared in
  let generics =
    List.filter_map
      (function Type_param p -> Some p | Row_param _ -> None)
      (in_order params order)
  in
  (ctx, generics @ implied)

(* A row variable, whose name no value parameter of its list or its impl
   has (generics.value-parameters). *)
let declare_row ctx (n : name) =
  if List.mem n.desc effect_names then
    errorf ctx Code.e0501 n.loc "a row variable can't be named `%s`" n.desc
  else if is_primitive n.desc then
    errorf ctx Code.e0210 n.loc "`%s` is a primitive type name" n.desc;
  let scope =
    ctx.row_vars @ List.map (fun (s, (v, _)) -> (s, v)) ctx.value_params
  in
  let v, _ = declare ctx scope "a row variable" n in
  let row_vars =
    if List.mem_assoc n.desc scope then ctx.row_vars
    else (n.desc, v) :: ctx.row_vars
  in
  ({ ctx with row_vars }, v)

(* A function's generics, in order, then the type parameters that its member
   types imply. *)
let declare_generics ctx generics =
  let one (ctx, declared, order) : Ast.generic -> _ = function
    | Ast.Type_param ({ value = Some _; _ } as p) ->
        declare_param (ctx, declared, order) p
    | Ast.Type_param p ->
        let v, type_params =
          declare ctx ctx.type_params "a type parameter" p.name
        in
        (* variadics.packs and variadics.advanced-tier: a pack, which makes its module advanced. *)
        if p.pack then advanced ctx;
        let packs = if p.pack then v.id :: ctx.packs else ctx.packs in
        ( { ctx with type_params; packs },
          declared @ [ (p, v) ],
          order @ [ Type_var v ] )
    | Row_param n ->
        let ctx, v = declare_row ctx n in
        (ctx, declared, order @ [ Row_var v ])
  in
  let ctx, declared, order = List.fold_left one (ctx, [], []) generics in
  let ctx, params, implied = bound_params ctx ~impl:false declared in
  (ctx, in_order params order @ List.map (fun p -> Type_param p) implied)

(* traits.where: a [where] clause bounds member types, and adds its bounds
   to the type parameters that they are among [params]. A bound on anything
   else is E0336, and so is the clause of a function whose signature is a
   trait's; the bound of a plain type parameter still holds, so that its uses
   report nothing more. *)
let bound_where ctx (params, checked) (wb : Ast.where_bound) =
  let loc = (List.hd wb.bounded).loc in
  let target = resolve_ty ctx { desc = Ty_named (wb.bounded, []); loc } in
  (match (wb.bounded, target.desc) with
  | [ n ], Ty_param _ ->
      errorf ctx Code.e0336 loc
        "`%s` is a type parameter, so its bound goes beside it, as `<%s: …>`"
        n.desc n.desc
  | [ _ ], Ty_error | _ :: _ :: _, _ | [], _ -> ()
  | [ _ ], _ ->
      errorf ctx Code.e0336 loc
        "a `where` clause bounds member types, such as `C.Item`");
  let traits, records = split_bounds wb.bounds in
  let resolved =
    List.map (resolve_bound ctx ~implied_by:(dotted_path wb.bounded)) traits
  in
  let added = List.map (fun r -> r.bound) resolved in
  let fields = List.concat_map (record_bound ctx) records in
  let own =
    match target.desc with
    | Ty_param v -> List.exists (fun p -> p.var.id = v.id) params
    | _ -> false
  in
  let params =
    List.map
      (fun p ->
        match target.desc with
        | Ty_param v when v.id = p.var.id ->
            { p with bounds = p.bounds @ added; fields = p.fields @ fields }
        | _ -> p)
      params
  in
  (* A member type that a bound's argument fixes, or one of an inherent
     block's parameter, is checked or assumed where it stands. *)
  let checked =
    match (wb.bounded, target.desc) with
    | _, Ty_error | [ _ ], _ -> checked
    | _ when own -> checked
    | _ -> checked @ List.map (fun b -> (target, b, loc)) added
  in
  (params @ List.concat_map (fun r -> r.implied) resolved, checked)

(* traits.where: the type parameters with what a [where] clause adds to
   them, and the bounds it puts on other types, each with its place. *)
let resolve_where ctx (w : Ast.where_ option) params =
  match w with
  | None -> (params, [])
  | Some w when ctx.fixed ->
      advanced ctx;
      errorf ctx Code.e0336 w.loc
        "a function of a trait or of a trait impl has the trait's signature, \
         so it takes no `where` clause";
      (params, [])
  | Some w ->
      advanced ctx;
      List.fold_left (bound_where ctx) (params, []) w.desc

(* The type parameters among a function's generics, with what [where] adds
   to them. *)
let where_generics ctx (w : Ast.where_ option) generics =
  let params =
    List.filter_map
      (function Type_param p -> Some p | Row_param _ -> None)
      generics
  in
  let params, checked = resolve_where ctx w params in
  let written (p : type_param) =
    List.exists
      (function Type_param q -> q.var.id = p.var.id | Row_param _ -> false)
      generics
  in
  ( List.map
      (function
        | Type_param p ->
            Type_param (List.find (fun q -> q.var.id = p.var.id) params)
        | Row_param v -> Row_param v)
      generics
    @ List.filter_map
        (fun p -> if written p then None else Some (Type_param p))
        params,
    checked )
