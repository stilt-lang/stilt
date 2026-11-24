(* Written effect rows (effects.rows; facts.implicit-effects), the effects they
   hold (handlers.effects-in-rows; tasks.async), and handler types (handlers.handler-types). *)

open Hir
open Resolve_context
open Resolve_paths

(* facts.implicit-effects, and effects.effect-names *)
let implicit_effects = [ "panic"; "alloc" ]

(* program.private-in-signatures: a private item can't appear in a signature that other
   modules see. *)
let check_public ctx loc (item : item) e =
  if ctx.public && item.home = ctx.scope.name && not e.pub then
    errorf ctx Code.e0214 loc
      "`%s` is private, but appears in a signature that other modules see"
      item.name

(* tasks.async and tasks.advanced-tier: [async], which makes the module advanced. *)
let async_effect ctx at =
  advanced ctx;
  { eff = Types.async_effect; args = []; at }

(* handlers.effects-in-rows and handlers.advanced-tier: the effect that [path] names, with its type
   arguments, which [ty] resolves. Naming one makes the module advanced. *)
let named_effect ctx ~ty (path : name list) args =
  let at = (List.hd path).loc in
  advanced ctx;
  match walk_to_end ctx ~want:Types ~noun:"an effect" path with
  | Broken_ref, _ -> None
  | Item_ref (item, ({ kind = Effect_item; _ } as e)), _ ->
      check_public ctx at item e;
      let args = List.map (ty ctx) args in
      let given = List.length args in
      if given = e.arity then Some { eff = item; args; at }
      else (
        errorf ctx Code.e0300 at "`%s` takes %d type argument%s, not %d"
          (dotted_path path) e.arity
          (if e.arity = 1 then "" else "s")
          given;
        None)
  | m, last ->
      wrong_kind ctx last m "an effect";
      None

let effect_ref ctx ~ty : Ast.effect_ref -> effect_inst option = function
  | Effect_named (path, args) -> named_effect ctx ~ty path args
  | Effect_async at -> Some (async_effect ctx at)

(* handlers.effects-in-rows: a row holds at most one instance of an effect. *)
let add_effect ctx (r : row) (e : effect_inst) =
  if List.exists (fun (f : effect_inst) -> f.eff = e.eff) r.effects then (
    errorf ctx Code.e0515 e.at
      "`%s` is already in this row, which holds one instance of an effect"
      e.eff.name;
    r)
  else { r with effects = r.effects @ [ e ] }

let resolve_row ctx ~ty (row : Ast.row) : row =
  let add (r : row) : Ast.row_elem -> row = function
    | Row_io loc ->
        if r.io then (
          errorf ctx Code.e0500 loc "`io` is already in this row";
          r)
        else { r with io = true }
    | Row_raise (loc, t) -> (
        let t = ty ctx t in
        match r.raise with
        | Some _ ->
            errorf ctx Code.e0500 loc "a row holds at most one `raise` label";
            r
        | None -> { r with raise = Some t })
    | Row_async loc -> add_effect ctx r (async_effect ctx loc)
    | Row_effect (path, args) -> (
        match named_effect ctx ~ty path args with
        | Some e -> add_effect ctx r e
        | None -> r)
    | Row_var n -> (
        match (List.assoc_opt n.desc ctx.row_vars, r.var) with
        | Some _, Some _ ->
            errorf ctx Code.e0500 n.loc "a row holds at most one row variable";
            r
        | Some v, None -> { r with var = Some v }
        | None, _ when List.mem n.desc implicit_effects ->
            errorf ctx Code.e0501 n.loc
              "`%s` is an implicit effect, which is never written" n.desc;
            r
        | None, _ ->
            unknown_name ctx ~name:n.desc n.loc "unknown row variable `%s`"
              n.desc;
            r)
  in
  List.fold_left add { io = false; raise = None; var = None; effects = [] } row

(* handlers.handler-types and handlers.advanced-tier: a handler's type, which makes the module
   advanced. *)
let handler_type ctx ~ty e answer row =
  advanced ctx;
  match effect_ref ctx ~ty e with
  | Some e -> Ty_handler (e, Option.map (ty ctx) answer, resolve_row ctx ~ty row)
  | None -> Ty_error
