(* Calls: of functions, variants, members, methods and function values. *)

module T = Types
module A = Tast
open Check_state
open Check_expect
open Check_effects
open Check_types
open Check_fields
open Check_members

(* A call by name: a place when the callee is a projection (projections.call-is-place). *)
let call_node ~projection callee targs args row ret loc =
  if projection then node (A.Project (callee, targs, args, row)) ret loc
  else node (A.Call (callee, targs, args, row)) ret loc

(* expressions.arguments and expressions.inout-arguments, and variadics.spread-expressions: a spread among the
   parameters or the arguments stands for any number of them. *)
let rec arguments ctx loc params (args : Hir.arg list) : A.arg list =
  if
    List.exists (fun (_, t) -> Packs.is_spread t) params
    || List.exists (fun (a : Hir.arg) -> Check_spreads.is_spread a.value) args
  then Check_spreads.spread_arguments ctx loc params args
  else fixed_arguments ctx loc params args

and fixed_arguments ctx loc params (args : Hir.arg list) : A.arg list =
  let st = ctx.st in
  if List.length params <> List.length args then (
    error st Code.e0315 loc "this takes %d argument%s, but %d %s given"
      (List.length params)
      (if List.length params = 1 then "" else "s")
      (List.length args)
      (if List.length args = 1 then "is" else "are");
    List.map
      (fun (a : Hir.arg) ->
        {
          A.mode = (if a.inout then by_inout else by_value);
          value = abandon ctx a.value;
        })
      args)
  else
    List.map2
      (fun (mode, ty) (a : Hir.arg) ->
        let v =
          match mode with
          | Ast.Inout when a.inout && not (may_be_place a.value) ->
              error st Code.e0401 a.value.loc
                "only a variable, a field, an element or a projection's call \
                 can be passed `inout`";
              abandon ctx a.value
          | Ast.Inout ->
              let v = infer ctx (Some ty) a.value in
              if a.inout && not (checked_place a.value v) then (
                error st Code.e0401 a.value.loc
                  "only a variable, a field, an element or a projection's call \
                   can be passed `inout`";
                { v with ty = T.Error })
              else if a.inout && through_option v then (
                error st Code.e0401 a.value.loc
                  "a field read through an `Option` is a copy, so it can't be \
                   passed `inout`";
                v)
              else (
                (* The callee writes the place back, so its type is the
                   parameter's exactly (effects.inout-function-arguments). *)
                expect st a.value.loc ~expected:ty v.ty;
                v)
          | Let -> check ctx ty a.value
        in
        (match (mode, a.inout) with
        | Ast.Inout, false ->
            error st Code.e0400 a.value.loc
              "this parameter is `inout`, so its argument is marked `inout`"
        | Let, true ->
            error st Code.e0400 a.value.loc
              "this parameter isn't `inout`, so its argument isn't marked"
        | _ -> ());
        { A.mode; value = v })
      params args

(* A call that can't be checked, whose arguments are checked as the error
   type. *)
let give_up ctx loc (args : Hir.arg list) =
  List.iter (fun (a : Hir.arg) -> ignore (abandon ctx a.value)) args;
  error_node loc

(* The receiver [r] of a method whose [self] has the mode [mode], as an
   argument. *)
let receiver_arg st (receiver : Hir.expr) (r : A.expr) mode =
  if mode = by_inout && not (checked_place receiver r && not (through_option r))
  then
    error st Code.e0401 receiver.loc
      "this method takes `inout self`, so its receiver must be a variable, a \
       field, an element or a projection's call";
  { A.mode; value = r }

(* A call of a member [m] of the inherent impls of the receiver's type
   [ty]. *)
let inherent_call ctx loc (receiver : Hir.expr) r ty (name : Hir.name)
    (m : Env.member) args =
  let st = ctx.st in
  match m.kind with
  | Method mode ->
      require_visible st name m;
      let targs, params, ret, row =
        instantiate st name.loc m.signature ~self:None ~use_at:loc
      in
      let self_ty, rest =
        match params with p :: rest -> (snd p, rest) | [] -> (T.Error, [])
      in
      expect st receiver.loc ~expected:self_ty ty;
      let args = arguments ctx loc rest args in
      perform ctx row loc;
      Check_foreign.used st loc (Member (m.owner, m.name)) targs;
      call_node ~projection:m.signature.projection
        (Member (m.owner, m.name))
        targs
        (receiver_arg st receiver r mode :: args)
        row ret loc
  | Function ->
      error st Code.e0314 name.loc
        "`%s` takes no `self`, so it is called as `%s.%s(…)`" name.desc
        m.owner.name name.desc;
      give_up ctx loc args
  | Constant ->
      error st Code.e0314 name.loc "`%s` is a constant, written `%s.%s`"
        name.desc m.owner.name name.desc;
      give_up ctx loc args

(* A call of the method [m] of [trait], which the receiver's type [ty]
   implements. A constructor trait's [Self] is the constructor at the head of
   [ty], and its receiver's type the trait writes (traits.constructor-traits and traits.receiver-types). *)
let trait_call ctx loc (receiver : Hir.expr) r ty (name : Hir.name) trait
    (m : Env.trait_method) (info : Env.trait_info) args =
  let st = ctx.st in
  let self = trait_self info ty in
  let targs, params, ret, row =
    instantiate_trait st name.loc ~use_at:loc trait m info self
  in
  obligation st self trait name.loc;
  let mode, rest =
    match params with
    | (mode, written) :: rest ->
        if info.arity > 0 then expect st receiver.loc ~expected:written ty;
        (mode, rest)
    | [] -> (by_value, [])
  in
  let args = arguments ctx loc rest args in
  improve st;
  perform ctx row loc;
  call_node ~projection:m.method_sig.projection
    (Trait_method (trait, m.method_name, self))
    targs
    (receiver_arg st receiver r mode :: args)
    row ret loc

(* traits.functions-without-self and traits.trait-constants: a trait's function without [self], or its constant,
   named after a value. *)
let not_a_method ctx loc (name : Hir.name) (m : Env.trait_method) args =
  let st = ctx.st in
  (match m.member_kind with
  | Constant ->
      error st Code.e0314 name.loc "`%s` is a constant, written `T.%s`"
        name.desc name.desc
  | Function | Method _ ->
      error st Code.e0314 name.loc
        "`%s` takes no `self`, so it is called as `T.%s(…)`" name.desc name.desc);
  give_up ctx loc args

(* The call [r.name(…)] where the type [ty] of [r] has no method [name]. *)
let field_call ctx loc (receiver : Hir.expr) r (ty : T.ty) (name : Hir.name)
    args =
  let st = ctx.st in
  (* A field, or a tuple's element, that holds a function. *)
  let field =
    match (int_of_string_opt name.desc, ty) with
    | Some i, Tuple ts when i < List.length ts ->
        Some (A.Tuple_field (r, i), List.nth ts i)
    | Some _, _ -> None
    | None, _ ->
        Option.map
          (fun t -> (A.Field (r, name.desc), t))
          (Option.bind (record_fields st ty) (List.assoc_opt name.desc))
  in
  match field with
  | Some (desc, field_ty) -> (
      let f = instantiated st None (node desc field_ty name.loc) in
      match T.resolve f.ty with
      | Fn (params, ret, row) ->
          let args = arguments ctx loc params args in
          perform ctx row loc;
          node (Call_value (f, args)) ret loc
      | t ->
          error st Code.e0311 name.loc "expected a function, found `%s`"
            (show t);
          give_up ctx loc args)
  | None ->
      if not (left_out st ty name.desc) then
        error st Code.e0314 name.loc "`%s` has no method `%s`" (show ty)
          name.desc;
      give_up ctx loc args

let method_call ctx loc receiver (name : Hir.name) args =
  let st = ctx.st in
  let r = infer ctx None receiver in
  match known st receiver.loc r.ty with
  | None -> give_up ctx loc args
  | Some ty -> (
      match find_method st ty name.desc with
      | Inherent m -> inherent_call ctx loc receiver r ty name m args
      | Via_trait (_, ({ member_kind = Function | Constant; _ } as m), _) ->
          not_a_method ctx loc name m args
      | Via_trait (trait, m, info) ->
          trait_call ctx loc receiver r ty name trait m info args
      | Ambiguous traits ->
          ambiguous st name traits;
          give_up ctx loc args
      | Missing -> field_call ctx loc receiver r ty name args)

(* A variant applied to its payload. *)
let variant_call ctx loc (callee : Hir.expr) item (args : Hir.arg list) =
  let st = ctx.st in
  match Env.variant st.env item with
  | Some (_, _, []) ->
      (* declarations.constructors: a variant without a payload is a value. *)
      error st Code.e0311 callee.loc
        "`%s` has no payload, so it is written without parentheses" item.name;
      List.iter (fun (a : Hir.arg) -> ignore (abandon ctx a.value)) args;
      error_node loc
  | Some (owner, _, payload) ->
      let ty, targs, info = instantiate_type st callee.loc owner in
      let payload =
        List.map (T.subst (List.combine info.params targs) []) payload
      in
      let args =
        arguments ctx loc (List.map (fun t -> (by_value, t)) payload) args
      in
      node
        (Construct (item, targs, List.map (fun (a : A.arg) -> a.value) args))
        ty loc
  | None -> error_node loc

(* A call of a function value. *)
let value_call ctx loc (callee : Hir.expr) (args : Hir.arg list) =
  let st = ctx.st in
  let f = infer ctx None callee in
  match T.resolve f.ty with
  | Fn (params, ret, row) ->
      let args = arguments ctx loc params args in
      perform ctx row loc;
      node (Call_value (f, args)) ret loc
  | Var _ ->
      let params =
        List.map
          (fun (a : Hir.arg) ->
            ((if a.inout then by_inout else by_value), fresh st a.value.loc))
          args
      in
      let ret = fresh st loc and row = T.fresh_row () in
      expect st callee.loc ~expected:(T.Fn (params, ret, row)) f.ty;
      let args = arguments ctx loc params args in
      perform ctx row loc;
      node (Call_value (f, args)) ret loc
  | Error ->
      List.iter (fun (a : Hir.arg) -> ignore (abandon ctx a.value)) args;
      error_node loc
  | t ->
      error st Code.e0311 callee.loc "expected a function, found `%s`" (show t);
      List.iter (fun (a : Hir.arg) -> ignore (abandon ctx a.value)) args;
      error_node loc

let call ctx loc (callee : Hir.expr) (args : Hir.arg list) =
  let st = ctx.st in
  match callee.desc with
  | Func item -> (
      match Env.function_sig st.env item with
      | Some s ->
          let targs, params, ret, row =
            instantiate st callee.loc s ~self:None ~use_at:callee.loc
          in
          let args = arguments ctx loc params args in
          improve st;
          perform ctx row loc;
          Check_foreign.used st loc (Function item) targs;
          call_node ~projection:s.projection (Function item) targs args row ret
            loc
      | None -> error_node loc)
  | Variant item -> variant_call ctx loc callee item args
  | Member (owner, name) -> (
      match member ctx callee.loc owner name with
      | Some (Callable (target, targs, params, ret, row, projection)) ->
          let args = arguments ctx loc params args in
          improve st;
          perform ctx row loc;
          Check_foreign.used st loc target targs;
          call_node ~projection target targs args row ret loc
      (* meta.shape-and-name *)
      | Some (Reflection (r, ty)) ->
          ignore (arguments ctx loc [] args);
          node (Reflect r) ty loc
      | Some (Trait_constant c) ->
          error st Code.e0311 callee.loc "expected a function, found `%s`"
            (show c.ty);
          List.iter (fun (a : Hir.arg) -> ignore (abandon ctx a.value)) args;
          error_node loc
      | None ->
          List.iter (fun (a : Hir.arg) -> ignore (abandon ctx a.value)) args;
          error_node loc)
  | Field (receiver, name) -> method_call ctx loc receiver name args
  | _ -> value_call ctx loc callee args
