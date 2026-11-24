(* Effects and handlers (handlers.declaring-effect and handlers.with): performances, handler literals, [with] and
   [resume]. *)

module T = Types
module A = Tast
open Check_state
open Check_unify
open Check_expect
open Check_effects
open Check_types

(* handlers.performing-operation: the type arguments of [eff] where it is performed: those of the
   row that the code must fit, as an enclosing [with] or the signature gives
   them, or new variables, which the first performance fixes. *)
let effect_args ctx loc eff (info : Env.effect_info) =
  match List.assoc_opt eff ctx.known with
  | Some args when List.length args = List.length info.eparams -> args
  | _ -> List.map (fun _ -> fresh ctx.st loc) info.eparams

(* An operation's parameters, result and row, for the effect's arguments. *)
let operation_sig (info : Env.effect_info) args (o : Env.operation_sig) =
  let types = List.combine info.eparams args in
  ( List.map (fun (m, t) -> (m, T.subst types [] t)) o.op_params,
    T.subst types [] o.op_ret,
    T.subst_row types [] o.op_row )

(* handlers.performing-operation: [Effect.op(…)] performs the operation: its effect, and its own
   row. *)
let perform_op ctx loc (callee : Hir.expr) eff (name : Hir.name) args =
  let st = ctx.st in
  match Env.effect_info st.env eff with
  | None -> Check_calls.give_up ctx loc args
  | Some info -> (
      match List.assoc_opt name.desc info.ops with
      | None ->
          error st Code.e0314 name.loc "`%s` has no operation `%s`" eff.name
            name.desc;
          Check_calls.give_up ctx loc args
      | Some o ->
          let targs = effect_args ctx callee.loc eff info in
          let params, ret, row = operation_sig info targs o in
          let args = Check_calls.arguments ctx loc params args in
          let row =
            if List.mem_assoc eff row.effects then row
            else { row with effects = (eff, targs) :: row.effects }
          in
          perform ctx row loc;
          node (Call (Operation (eff, name.desc), targs, args, row)) ret loc)

(* handlers.performing-operation: an operation is performed by a call, and is no value. *)
let operation_value ctx loc (eff : Hir.item) (name : Hir.name) =
  error ctx.st Code.e0311 loc
    "`%s.%s` is an operation, which is performed by a call: `%s.%s(…)`" eff.name
    name.desc eff.name name.desc;
  error_node loc

(* handlers.handler-literals: whether the operation [f] implements is [o]'s, with its types:
   the same parameters, in the same modes, and the same result. *)
let implements st args info (o : Env.operation_sig) (f : Hir.handler_op) =
  let params, ret, _ = operation_sig info args o in
  f.op_plain
  && List.length params = List.length f.op_params
  && List.for_all2
       (fun (m, t) (n, _, written) -> m = n && unify (of_hir st written) t)
       params f.op_params
  && unify (Option.fold ~none:T.unit ~some:(of_hir st) f.op_ret) ret

(* handlers.handler-literals: the first operation that a literal misses, implements twice or
   with other types, or that the effect doesn't declare. *)
let mismatched st args (info : Env.effect_info) (ops : Hir.handler_op list) =
  let names = List.map (fun (f : Hir.handler_op) -> f.op_name.desc) ops in
  let twice n = List.length (List.filter (( = ) n) names) > 1 in
  match List.find_opt (fun (n, _) -> not (List.mem n names)) info.ops with
  | Some (n, _) -> Some ("it misses the operation `" ^ n ^ "`")
  | None ->
      List.find_map
        (fun (f : Hir.handler_op) ->
          let n = f.op_name.desc in
          match List.assoc_opt n info.ops with
          | None -> Some ("the effect declares no operation `" ^ n ^ "`")
          | Some _ when twice n -> Some ("it implements `" ^ n ^ "` twice")
          | Some o when not (implements st args info o f) ->
              Some ("its `" ^ n ^ "` has other types than the effect's")
          | Some _ -> None)
        ops

(* handlers.handler-literals and handlers.resuming: an operation's body, as a closure literal of the
   function that writes the handler. Its effects are its operation's row's,
   and what the handler's row [hrow] holds. One that takes control, with
   [answer], has the type [R], and may [resume]. *)
let operation ctx ~answer ~hrow info args (f : Hir.handler_op) =
  let st = ctx.st in
  let o = List.assoc f.op_name.desc info.Env.ops in
  let params, ret, row = operation_sig info args o in
  let patterns =
    List.map2
      (fun (_, (v : Hir.var), _) (_, t) : A.pattern ->
        Hashtbl.replace st.locals v.id t;
        { pat = P_bind v; pty = t; ploc = v.loc })
      f.op_params params
  in
  let body_ty = Option.value answer ~default:ret in
  let resume = Option.map (fun r -> (ret, r)) answer in
  let inner =
    {
      ctx with
      ret = body_ty;
      yields = None;
      effects = ref [];
      known = row.effects;
      resume;
    }
  in
  let b, _ =
    Check_blocks.block_expr inner ~at:f.op_name.loc (Some body_ty) f.op_body
  in
  let fits = { row with tail = hrow.T.tail } in
  settle st !(inner.effects) fits;
  ( f.op_name.desc,
    node
      (Closure (patterns, [], node (Block b) body_ty f.op_name.loc))
      (T.Fn (params, body_ty, fits))
      f.op_name.loc )

(* handlers.handler-literals: the literal of a handler of [inst], whose arguments the literal
   writes or inference gives, as the expected type does. Its row holds
   what its bodies perform beyond their operations' rows: [io], and its own
   effect, which they perform on the handler outside it (handlers.with). Anything
   else is E0502 in the body. *)
let literal ctx expected loc (h : Hir.handler_lit) (inst : Hir.effect_inst)
    (info : Env.effect_info) =
  let st = ctx.st in
  let args =
    match inst.args with
    | [] -> List.map (fun _ -> fresh st inst.at) info.eparams
    | args -> List.map (of_hir st) args
  in
  let answer = Option.map (of_hir st) h.answer in
  (match Option.map T.resolve expected with
  | Some (Handler e) when e.eff = inst.eff -> ignore (unify_all args e.hargs)
  | _ -> ());
  match mismatched st args info h.ops with
  | Some why ->
      error st Code.e0511 inst.at "this handler doesn't match `%s`: %s"
        inst.eff.name why;
      error_node loc
  | None ->
      let hrow = T.fresh_row ~least:true () in
      Option.iter
        (fun rv ->
          T.add_upper rv
            ( { T.empty_row with io = true; effects = [ (inst.eff, args) ] },
              Nothing ))
        (open_var hrow);
      let ops = List.map (operation ctx ~answer ~hrow info args) h.ops in
      node
        (Handler { heffect = inst.eff; control = Option.is_some answer; ops })
        (T.Handler { eff = inst.eff; hargs = args; answer; hrow })
        loc

let handler_lit ctx expected loc (h : Hir.handler_lit) =
  let st = ctx.st in
  match (h.async_at, h.heffect) with
  | Some at, _ ->
      (* tasks.async *)
      error st Code.e0511 at
        "`async` is handled by `task.threads()` or `task.sequential()`, which \
         start tasks; a handler literal can't";
      error_node loc
  | None, None ->
      st.broken <- true;
      error_node loc
  | None, Some inst -> (
      match Env.effect_info st.env inst.eff with
      | Some info -> literal ctx expected loc h inst info
      | None ->
          st.broken <- true;
          error_node loc)

(* handlers.resuming and handlers.resume-outside-operation: [resume(v)], in an operation's body of a handler that takes
   control, and E0513 anywhere else. *)
let resume_expr ctx loc value =
  let st = ctx.st in
  match ctx.resume with
  | None ->
      error st Code.e0513 loc
        "`resume` belongs in an operation of a handler that takes control, \
         written `handler E -> R { … }`";
      Option.iter (fun v -> ignore (abandon ctx v)) value;
      error_node loc
  | Some (op_ret, answer) ->
      let v =
        match value with
        | Some e -> Some (check ctx op_ret e)
        | None ->
            expect st loc ~expected:op_ret T.unit;
            None
      in
      node (Resume v) answer loc
