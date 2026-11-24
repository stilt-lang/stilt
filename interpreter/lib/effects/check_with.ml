(* [with] (handlers.with and handlers.resuming). *)

module T = Types
module A = Tast
open Check_state
open Check_unify
open Check_expect
open Check_effects

(* The position of a block's value, where E0311 reports one that isn't the
   [R] of a handler that takes control. *)
let value_at loc (b : Hir.block) =
  match List.rev b with { desc = Expr e; _ } :: _ -> e.loc | _ -> loc

(* handlers.with: the effects that the rows of the operations of a handler of
   [hty] hold, each once, which its bodies perform on the handlers outside the
   [with] that installs it. A raise or [io] of those rows is the performance's,
   whose row holds it (handlers.performing-operation). *)
let operation_effects st (hty : T.handler) =
  match Env.effect_info st.env hty.eff with
  | Some info when List.length info.eparams = List.length hty.hargs ->
      let types = List.combine info.eparams hty.hargs in
      let add effects (e, args) =
        if List.mem_assoc e effects then effects else effects @ [ (e, args) ]
      in
      let effects =
        List.fold_left
          (fun acc (_, (o : Env.operation_sig)) ->
            List.fold_left add acc (T.subst_row types [] o.op_row).effects)
          [] info.ops
      in
      { T.empty_row with effects }
  | _ -> T.empty_row

(* handlers.with: the block, run with the handler [h] of type [hty] installed. Its
   effects reach the [with] without the handled effect, whose arguments
   must be the handler's, and the [with] performs them, the handler type's
   row and its operations' effects. With [-> R], the block, and so the
   [with], has type [R] (handlers.resuming). *)
let installed ctx expected loc ~at (hv : A.expr) (hty : T.handler) body =
  let st = ctx.st in
  let inner =
    { ctx with effects = ref []; known = (hty.eff, hty.hargs) :: ctx.known }
  in
  let b, ty =
    match hty.answer with
    | None -> body inner expected
    | Some r ->
        let b, t = body inner None in
        (b, if fits st at ~expected:r t then r else T.Error)
  in
  let passed = T.fresh_row () in
  let report = reporter st in
  List.iter
    (fun (row, at) ->
      report at (fit ~handled:(Effect_of (hty.eff, hty.hargs)) row passed))
    (List.rev !(inner.effects));
  perform ctx passed loc;
  perform ctx hty.hrow loc;
  perform ctx (operation_effects st hty) loc;
  node (With (hv, hty.eff, hty.hargs, b)) ty loc

(* A [with] whose handler has an error, or isn't a handler: its block is
   checked, and the [with] has the error type. *)
let broken ctx expected body =
  let inner = { ctx with effects = ref [] } in
  ignore (body inner expected);
  ctx.st.broken <- true;
  T.Error

let one ctx expected loc ~at (h : Hir.expr) body =
  let st = ctx.st in
  let hv = infer ctx None h in
  match known st h.loc hv.ty with
  | Some (Handler hty) -> installed ctx expected loc ~at hv hty body
  | Some t ->
      error st Code.e0311 h.loc "expected a handler, found `%s`" (show t);
      { (error_node loc) with ty = broken ctx expected body }
  | None -> { (error_node loc) with ty = broken ctx expected body }

(* handlers.with: [with a, b { … }] is [with a { with b { … } }]. *)
let rec with_expr ctx expected loc (handlers : Hir.expr list)
    (block : Hir.block) =
  match handlers with
  | [] -> invalid_arg "Check_with.with_expr"
  | [ h ] ->
      let at = value_at loc block in
      one ctx expected loc ~at h (fun ctx expected ->
          Check_blocks.block_expr ctx ~at expected block)
  | h :: rest ->
      one ctx expected loc ~at:loc h (fun ctx expected ->
          let w = with_expr ctx expected loc rest block in
          ([ { A.stmt = Expr w; at = loc } ], w.ty))
