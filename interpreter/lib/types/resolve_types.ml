(* Written types, effect rows and bounds (declarations.type-arguments; effects.rows;
   traits.impl-blocks; traits.bound-arguments, traits.member-types and traits.constructor-traits). *)

open Hir
open Resolve_context
open Resolve_paths

(* facts.implicit-effects, and effects.effect-names *)
let implicit_effects = Resolve_rows.implicit_effects
let effect_names = "io" :: implicit_effects

(* Types *)

let check_public = Resolve_named.check_public
let as_type = Resolve_named.as_type
let plural = Resolve_named.plural
let arity_error = Resolve_named.arity_error
let named = Resolve_named.named

(* Bounds *)

type resolved_bound = {
  bound : bound;
  implied : type_param list;
      (* The type parameters that its member types name, for a bound written
         without the trait's arguments (traits.member-types). *)
  arity : int;
      (* Its trait's arity as a constructor trait (traits.constructor-traits). *)
  params : string list; (* Its trait's parameters. *)
  at : loc;
}

(* polymorphism.function-types: whether the type parameter [v] appears in [t], counting
   the raises of its rows unless [rows] is false, as generics.value-parameters-determined asks of a
   value parameter. *)
let rec mentions ?(rows = true) (v : var) (t : ty) =
  let mentions = mentions ~rows in
  match t.desc with
  | (Ty_param w | Ty_app (w, _)) when w.id = v.id -> true
  | Ty_con (_, ts) | Ty_tuple ts | Ty_app (_, ts) | Ty_self_app ts ->
      List.exists (mentions v) ts
  | Ty_record fields ->
      List.exists (fun (f : field_decl) -> mentions v f.ty) fields
  | Ty_spread (_, t) -> mentions v t
  | Ty_fn (_, ps, ret, row) ->
      List.exists (fun (_, t) -> mentions v t) ps
      || Option.fold ~none:false ~some:(mentions v) ret
      || (rows && Option.fold ~none:false ~some:(mentions v) row.raise)
  | Ty_handler (e, ret, _) ->
      List.exists (mentions v) (e.args @ Option.to_list ret)
  | Ty_param _ | Ty_self | Ty_value _ | Ty_error -> false

(* polymorphism.placement: a polymorphic function type is the type of a parameter, a
   field or a payload, which [poly] says the type [t] is. *)
let placed ctx ~poly (t : Ast.ty) =
  match t.desc with
  | Ty_fn (_ :: _, _, _, _) when not poly ->
      errorf ctx Code.e0340 t.loc
        "a polymorphic function type is the type of a parameter, a field or a \
         payload, not of this";
      false
  | _ -> true

(* records.open-parameter-types: an open record type stands for a type the caller gives,
   which only a parameter's type is. *)
let open_out_of_place ctx loc =
  errorf ctx Code.e0341 loc
    "an open record type stands for a type the caller gives, so only a \
     parameter has one; name a type parameter with this bound, as `<P: { … \
     }>`, and write `P`";
  Ty_error

let rec has_error (t : ty) =
  match t.desc with
  | Ty_error -> true
  | Ty_con (_, ts) | Ty_tuple ts | Ty_app (_, ts) | Ty_self_app ts ->
      List.exists has_error ts
  | Ty_record fields ->
      List.exists (fun (f : field_decl) -> has_error f.ty) fields
  | Ty_spread (_, t) -> has_error t
  | Ty_fn (_, ps, ret, _) ->
      List.exists (fun (_, t) -> has_error t) ps
      || Option.fold ~none:false ~some:has_error ret
  | Ty_handler (e, ret, _) -> List.exists has_error (e.args @ Option.to_list ret)
  | Ty_param _ | Ty_self | Ty_value _ -> false

let rec resolve_ty ?(poly = false) ctx (t : Ast.ty) : ty =
  let placed = placed ctx ~poly t in
  let desc =
    match t.desc with
    | Ty_named (path, args) -> named ctx t.loc path (type_args ctx args)
    (* generics.value-arguments: a value stands only among a type's arguments. *)
    | Ty_int _ | Ty_bool _ -> Ty_error
    | Ty_tuple ts -> tuple ctx ts
    | Ty_record (fields, false) -> Ty_record (record_fields ctx fields)
    | Ty_record (fields, true) ->
        (* A name in it that resolves to nothing is reported too: it is no part
           of the error (errors.unknown-names, "Unknown names"). *)
        ignore (record_fields ctx fields);
        open_out_of_place ctx t.loc
    | Ty_spread body -> spread ctx t.loc body
    | Ty_fn (generics, params, ret, row) -> fn_type ctx generics params ret row
    | Ty_handler (e, ret, row) ->
        Resolve_rows.handler_type ctx
          ~ty:(fun ctx t -> resolve_ty ctx t)
          e ret row
    | Ty_macro (path, group) -> macro_type ctx t.loc path group
    | Ty_splice s -> Resolve_macros.splice ctx In_type s Ty_error
  in
  { desc = (if placed then desc else Ty_error); loc = t.loc }

(* macros.procedural-uses: a use of a macro whose result is a type, expanded in its
   place. *)
and macro_type ctx loc path group =
  match
    Resolve_macros.expand ctx loc path [ group ] Macro_expand.Type
      (fun ctx tokens ->
        Macro_expand.parse_type ~file:ctx.scope.file ~at:loc tokens)
      (fun ctx t -> resolve_ty ctx t)
  with
  | Some t -> t.desc
  | None -> Ty_error

(* A tuple type. A spread in it whose type is an error leaves the tuple's
   length unknown, so the tuple has the error type, from which no diagnostic
   arises (errors.error-type). *)
and tuple ctx (ts : Ast.ty list) =
  let elems = List.map (resolve_ty ctx) ts in
  let lost (a : Ast.ty) (r : ty) =
    match (a.desc, r.desc) with Ty_spread _, Ty_error -> true | _ -> false
  in
  if List.exists2 lost ts elems then Ty_error else Ty_tuple elems

(* generics.value-arguments: the arguments of a type whose head [walked] names, each
   read as a value for a value parameter and as a type for a type parameter.
   The arguments of a head with an error, or of a path that goes on past a
   name that isn't a module, are read as either, so that only those that are
   neither report errors. *)
and type_args ctx (args : Ast.ty list) walked =
  let resolve = function
    | Broken_ref, _, _ | _, _, _ :: _ -> fun _ a -> loose_arg ctx a
    | Item_ref (item, { kind = Type_item; values; _ }), _, [] -> (
        fun i (a : Ast.ty) ->
          match List.assoc_opt i values with
          | Some expected ->
              let size = item = Resolve_values.array_item && i = 1 in
              {
                desc = Resolve_values.value_arg ctx ~size expected a;
                loc = a.loc;
              }
          | None -> type_arg ctx a)
    | _ -> fun _ a -> type_arg ctx a
  in
  List.mapi (resolve walked) args

(* A type given for a type parameter. *)
and type_arg ctx (a : Ast.ty) =
  let misplaced what =
    Resolve_values.not_a_type ctx a what;
    { desc = Ty_error; loc = a.loc }
  in
  match (Resolve_values.type_arg_misplaced ctx a, a.desc) with
  | Some what, _ -> misplaced what
  | None, Ty_named (path, args) ->
      let misplaced (n : name) what =
        ignore (misplaced (Printf.sprintf "`%s` is %s" n.desc what))
      in
      {
        desc = named ctx ~misplaced a.loc path (type_args ctx args);
        loc = a.loc;
      }
  | None, _ -> resolve_ty ctx a

(* An argument of a type whose head has an error, which may be a type or a
   value. *)
and loose_arg ctx (a : Ast.ty) =
  let quiet = { desc = Ty_error; loc = a.loc } in
  match a.desc with
  | Ty_int _ | Ty_bool _ -> quiet
  | Ty_named ([ n ], []) when List.mem_assoc n.desc ctx.value_params -> quiet
  | Ty_named (path, [])
    when Option.is_some (Resolve_values.constant_of ctx path) ->
      quiet
  | _ -> resolve_ty ctx a

(* records.anonymous-types: the fields of an anonymous record type, or of a record
   bound, each named once (E0316). *)
and record_fields ctx (fields : Ast.field_decl list) =
  advanced ctx;
  List.fold_left
    (fun kept ({ field; ty } : Ast.field_decl) ->
      let ty = resolve_ty ctx ty in
      (* A field is no name of a scope (macros.hygiene). *)
      let field = { field with desc = Macro_marks.base field.desc } in
      if List.exists (fun (f : field_decl) -> f.field.desc = field.desc) kept
      then (
        errorf ctx Code.e0316 field.loc "the field `%s` is named twice"
          field.desc;
        kept)
      else kept @ [ { field; ty } ])
    [] fields

(* variadics.type-spreads: a spread names exactly one pack, perhaps more than once,
   and stands inside no other spread. *)
and spread ctx loc body =
  match ctx.spread with
  | Some _ ->
      errorf ctx Code.e0343 loc "a spread can't stand inside another spread";
      Ty_error
  | None -> (
      let named = ref [] in
      let t = resolve_ty { ctx with spread = Some named } body in
      let named =
        List.sort_uniq (fun (a : var) b -> compare a.id b.id) !named
      in
      match
        List.partition (fun (v : var) -> List.mem v.id ctx.misplaced) named
      with
      | _ :: _, _ -> t.desc
      | [], named -> (
          match named with
          | [ v ] -> Ty_spread (v, t)
          | _ when has_error t -> Ty_error
          | [] ->
              errorf ctx Code.e0343 loc
                "this spread names no pack, so nothing says how many elements \
                 it stands for";
              Ty_error
          | a :: b :: _ ->
              errorf ctx Code.e0343 loc
                "this spread names two packs, `%s` and `%s`, which may differ \
                 in length; a spread names one"
                a.name b.name;
              Ty_error))

(* A function type, whose own type parameters are in scope in it alone, and
   each of which its parameters or its result names (polymorphism.function-types). Its
   parameters may have polymorphic function types (polymorphism.placement). *)
and fn_type ctx generics params ret row =
  if generics <> [] then advanced ctx;
  let inner, generics = poly_generics ctx generics in
  let written = params in
  let params =
    List.map (fun (m, t) -> (m, resolve_ty ~poly:true inner t)) params
  in
  let ret = Option.map (resolve_ty inner) ret in
  let row = resolve_row inner row in
  let unused (p : type_param) =
    let used =
      List.exists (fun (_, t) -> mentions p.var t) params
      || Option.fold ~none:false ~some:(mentions p.var) ret
    in
    if not used then
      errorf ctx Code.e0339 p.var.loc
        "`%s` appears in neither the parameters nor the result of this \
         function type, so no call could say what it is"
        p.var.name;
    not used
  in
  (* A spread whose type is an error leaves the number of parameters unknown,
     as a tuple's length (variadics.type-spreads). *)
  let lost =
    List.exists2
      (fun (_, (a : Ast.ty)) (_, (r : ty)) ->
        match (a.desc, r.desc) with Ty_spread _, Ty_error -> true | _ -> false)
      written params
  in
  (* A type with an unused parameter is the error type, as is any part of a
     signature with an error (errors.error-type). *)
  if List.exists Fun.id (List.map unused generics) || lost then Ty_error
  else Ty_fn (generics, params, ret, row)

(* polymorphism.function-types: the type parameters of a polymorphic function type, with
   their bounds, which may name one another. They are in scope in the type
   alone. One that the list repeats, or with the name of a type parameter
   already in scope, the enclosing function's or impl block's, is E0208, as a
   method's generic with its block's name is (traits.impl-blocks), and the name
   keeps its first meaning. *)
and poly_generics ctx (generics : Ast.type_param list) =
  let declare (scope, vars) (p : Ast.type_param) =
    let v = fresh ctx p.name in
    let named ((q : Ast.type_param), _) = q.name.desc = p.name.desc in
    if List.exists named vars || List.mem_assoc p.name.desc ctx.type_params then (
      errorf ctx Code.e0208 p.name.loc "`%s` is already a type parameter here"
        p.name.desc;
      (scope, vars))
    else ((p.name.desc, v) :: scope, vars @ [ (p, v) ])
  in
  let type_params, vars =
    List.fold_left declare (ctx.type_params, []) generics
  in
  (* variadics.packs: a polymorphic function type's parameters are never
     packs. One is a plain type parameter after E0344, so that nothing more
     is reported of it. *)
  let misplaced =
    List.filter_map
      (fun ((p : Ast.type_param), (v : var)) ->
        if p.pack then (
          errorf ctx Code.e0344 p.name.loc
            "a polymorphic function type's parameters are never packs";
          Some v.id)
        else None)
      vars
  in
  let inner = { ctx with type_params; misplaced = misplaced @ ctx.misplaced } in
  let param ((p : Ast.type_param), var) =
    let bounds = List.map (fun b -> resolve_bound inner b) p.bounds in
    List.iter
      (fun r ->
        if r.arity > 0 then
          errorf ctx Code.e0337 r.at
            "a trait over type constructors bounds only a function's generics")
      bounds;
    let bounds = List.map (fun r -> r.bound) bounds in
    { var; bounds; fields = []; pack = false; implied = false; value = None }
  in
  (inner, List.map param vars)

(* effects.rows, and facts.implicit-effects *)
and resolve_row ctx (row : Ast.row) : row =
  Resolve_rows.resolve_row ctx ~ty:(fun ctx t -> resolve_ty ctx t) row

(* traits.bound-arguments: a bound names a trait with all its arguments, or none,
   and then [implied_by] names the type parameter whose member types take
   their place. The trait of an impl, which has no [implied_by], is given all
   of them. *)
and resolve_bound ctx ?implied_by (b : Ast.bound) =
  match b with
  | Trait_bound { trait; args } -> trait_bound ctx ?implied_by trait args
  | Record_bound t ->
      (* records.record-bounds: a record bound bounds a type parameter of a function
         or an impl block, or a member type, and nothing else. A name in it
         that resolves to nothing is reported too (errors.unknown-names). *)
      ignore (record_bound_fields ctx t);
      errorf ctx Code.e0341 t.loc
        "a record bound bounds a type parameter of a function or an impl \
         block, or a member type, not this";
      {
        bound = { trait = Trait_error; args = [] };
        implied = [];
        arity = 0;
        params = [];
        at = t.loc;
      }

(* The fields of a record type written where no record bound may stand,
   resolved only for the diagnostics of their types. *)
and record_bound_fields ctx (t : Ast.ty) =
  match t.desc with
  | Ty_record (fields, _) -> record_fields ctx fields
  | _ -> []

(* records.bound-fields: the fields of a record bound, which ends with [..], since
   one that named every field would be a type (E0341). One without it still
   gives its fields, as the fix that adds [..] does, so that a field read
   through it is no second diagnostic (errors.root-causes). *)
and record_bound ctx (t : Ast.ty) =
  match t.desc with
  | Ty_record (fields, true) -> record_fields ctx fields
  | Ty_record (fields, false) ->
      let given = record_fields ctx fields in
      errorf ctx Code.e0341 t.loc
        "a record bound names the fields a record needs, so it ends with `..`, \
         as `{ %s, .. }`"
        (String.concat ", "
           (List.map (fun (f : Ast.field_decl) -> f.field.desc ^ ": …") fields));
      given
  | _ -> []

and trait_bound ctx ?implied_by (trait : name list) (written : Ast.ty list) =
  let at = (List.hd trait).loc in
  let error = { trait = Trait_error; args = [] } in
  let plain bound = { bound; implied = []; arity = 0; params = []; at } in
  (* A bound whose trait doesn't resolve bounds nothing, but its arguments
     are types all the same, so a name among them that resolves to nothing
     is reported (errors.unknown-names). *)
  let unbound () =
    List.iter (fun a -> ignore (resolve_ty ctx a)) written;
    plain error
  in
  match walk_to_end ctx ~want:Types ~noun:"a trait" trait with
  | Broken_ref, _ -> unbound ()
  | Item_ref (item, ({ kind = Trait_item; _ } as e)), _ -> (
      check_public ctx at item e;
      if e.advanced then advanced ctx;
      let args = List.map (resolve_ty ctx) written in
      let n = List.length e.params in
      let made bound implied =
        { bound; implied; arity = e.arity; params = e.params; at }
      in
      match (args, implied_by) with
      | [], Some owner when n > 0 ->
          let vars =
            List.map
              (fun p -> fresh ctx { desc = owner ^ "." ^ p; loc = at })
              e.params
          in
          made
            {
              trait = Trait_ref item;
              args = List.map (fun v -> { desc = Ty_param v; loc = at }) vars;
            }
            (List.map
               (fun var ->
                 {
                   var;
                   bounds = [];
                   fields = [];
                   pack = false;
                   implied = true;
                   value = None;
                 })
               vars)
      | _ when List.length args = n -> made { trait = Trait_ref item; args } []
      | _ ->
          ignore (arity_error ctx at trait n (List.length args));
          made
            {
              trait = Trait_ref item;
              args = List.map (fun _ -> { desc = Ty_error; loc = at }) e.params;
            }
            [])
  | m, last ->
      wrong_kind ctx last m "a trait";
      unbound ()

(* declarations.type-arguments, and traits.constructor-impls: the type of an impl of a constructor
   trait of [arity], a constructor of that arity written without
   arguments. *)
let constructor ctx arity (t : Ast.ty) =
  let wrong what =
    errorf ctx Code.e0337 t.loc
      "an impl of a trait over constructors of %d argument%s names such a \
       constructor without arguments, not %s"
      arity (plural arity) what;
    { desc = Ty_error; loc = t.loc }
  in
  match t.desc with
  | Ty_named (path, []) -> (
      match walk_to_end ctx ~want:Types ~noun:"a type" path with
      | Broken_ref, _ -> { desc = Ty_error; loc = t.loc }
      | Item_ref (item, ({ kind = Type_item; _ } as e)), _ when e.arity = arity
        ->
          check_public ctx t.loc item e;
          { desc = Ty_con (item, []); loc = t.loc }
      | Item_ref (item, { kind = Type_item; arity = a; _ }), _ ->
          wrong
            (Printf.sprintf "`%s`, which takes %d argument%s" item.name a
               (plural a))
      | m, last ->
          wrong_kind ctx last m "a type";
          { desc = Ty_error; loc = t.loc })
  | Ty_named _ -> wrong "a type with its arguments"
  | Ty_tuple _ | Ty_spread _ -> wrong "a tuple"
  | Ty_record _ -> wrong "a record type"
  | Ty_fn _ -> wrong "a function type"
  | Ty_handler _ -> wrong "a handler type"
  | Ty_int _ | Ty_bool _ -> wrong "a value"
  | Ty_macro _ | Ty_splice _ -> wrong "a macro's use"

(* The type a struct literal or a record pattern names (declarations.name-lookup). *)
let record_ty ctx (path : name list) : ty =
  let loc = (List.hd path).loc in
  let desc =
    match walk_to_end ctx ~want:Types ~noun:"a type" path with
    | Broken_ref, _ -> Ty_error
    | Param_ref v, _ -> Ty_param v
    | Self_ref t, _ -> t.desc
    | Item_ref (item, { kind = Type_item; _ }), _ -> Ty_con (item, [])
    | m, last ->
        wrong_kind ctx last m "a type";
        Ty_error
  in
  { desc; loc }
