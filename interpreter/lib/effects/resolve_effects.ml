(* Effects and handlers (handlers.declaring-effect, handlers.handler-literals and handlers.advanced-tier; tasks.async): the
   declarations of effects, and the operations of handler literals. *)

open Hir
open Resolve_context
open Resolve_types
open Resolve_patterns

(* An operation's parameters, bound by [b], with an error for a receiver,
   which only functions of impl and trait blocks take (handlers.declaring-effect), and
   for an [inout] one, which is then taken by value, so that a handler's
   operation that marks one is no mismatch as well (handlers.no-inout-parameter). *)
let params ctx b (ps : Ast.param list) =
  List.filter_map
    (function
      | Ast.Self_param (_, loc, _) ->
          errorf ctx Code.e0215 loc
            "an operation takes no `self`, since no value performs it";
          None
      | Param (mode, n, t, _) ->
          if mode = Ast.Inout then
            errorf ctx Code.e0517 n.loc
              "an operation takes `%s` by value, not `inout`: take it and \
               return the new value"
              n.desc;
          let t = resolve_ty ~poly:true ctx t in
          Some ((Let : Ast.mode), bind ctx b n, t))
    ps

(* Reports each name that an earlier one repeats (E0208). *)
let check_unique ctx (names : name list) =
  ignore
    (List.fold_left
       (fun seen (n : name) ->
         if Sset.mem n.desc seen then (
           errorf ctx Code.e0208 n.loc "`%s` is already an operation here"
             n.desc;
           seen)
         else Sset.add n.desc seen)
       Sset.empty names)

(* handlers.declaring-effect: an effect, whose type parameters are in scope in its
   operations, each named once, of which there is at least one (E0518).
   Declaring one makes the module advanced (handlers.advanced-tier). *)
let resolve_effect ctx ~public (e : Ast.effect_decl) : effect_decl =
  advanced ctx;
  if e.ops = [] then
    errorf ctx Code.e0518 e.name.loc
      "the effect `%s` declares no operation, so nothing can perform it"
      e.name.desc;
  let ctx, params_ =
    List.fold_left
      (fun (ctx, vars) (n : name) ->
        let v, type_params =
          Resolve_generics.declare ctx ctx.type_params "a type parameter" n
        in
        ({ ctx with type_params }, vars @ [ v ]))
      ({ ctx with public }, [])
      e.params
  in
  check_unique ctx (List.map (fun (o : Ast.operation) -> o.op_name) e.ops);
  let operation (o : Ast.operation) =
    {
      op = o.op_name;
      params = params ctx (binder ()) o.op_params;
      ret = Option.map (resolve_ty ctx) o.op_ret;
      row = resolve_row ctx o.op_row;
    }
  in
  { name = e.name; params = params_; ops = List.map operation e.ops }

(* handlers.handler-literals: an operation of a handler literal, written as a function.
   [block] resolves its body, in which its parameters are bound and no loop
   is open. *)
let resolve_op ctx ~block (f : Ast.fn_decl) =
  let b = binder () in
  let op_params = params ctx b f.params in
  let op_plain =
    f.generics = [] && (not f.projection) && Option.is_none f.where_
    && Option.is_none f.without
    && List.for_all (function Ast.Param _ -> true | _ -> false) f.params
  in
  let inner = { (with_bound ctx b) with in_loop = false } in
  let op_body =
    match f.body with
    | Some (Body (stmts, _)) -> block inner stmts
    | Some (Body_hole loc) -> [ { desc = Expr { desc = Hole; loc }; loc } ]
    | None -> []
  in
  {
    op_name = f.name;
    op_params;
    op_ret = Option.map (resolve_ty ctx) f.ret;
    op_row = resolve_row ctx f.row;
    op_plain;
    op_body;
  }

(* handlers.handler-literals and handlers.advanced-tier; tasks.async: a handler literal, whose effect is
   named, or is [async], which E0511 reports when it is checked. *)
let resolve_handler ctx ~block loc (e : Ast.effect_ref) answer fns =
  advanced ctx;
  let heffect, async_at =
    match e with
    | Effect_async _ -> (None, Some loc)
    | Effect_named _ ->
        (Resolve_rows.effect_ref ctx ~ty:(fun ctx t -> resolve_ty ctx t) e, None)
  in
  Handler
    {
      heffect;
      async_at;
      answer = Option.map (resolve_ty ctx) answer;
      ops = List.map (resolve_op ctx ~block) fns;
    }
