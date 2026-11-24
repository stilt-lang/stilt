(* effects.no-escape, no escape: a non-escaping parameter, and a closure literal
   that names one, may only be called, or passed on to a non-escaping
   parameter of the function or method that a call names, or E0508. A scope
   of [std.task] is checked as such a parameter is, but may only be passed to
   a parameter of type [Scope<E>], as the receiver of [s.spawn] is, or E0434
   (tasks.scope-that-escapes). *)

open Tast

let scope_item = { Hir.home = "std.task"; name = "Scope" }

let is_scope ty =
  match Types.resolve ty with Con (item, _) -> item = scope_item | _ -> false

(* The signature of what a call names. *)
let signature env = function
  | Function item -> Env.function_sig env item
  | Member (item, name) ->
      List.find_opt
        (fun (m : Env.member) -> m.name = name)
        (Env.inherent_members env item)
      |> Option.map (fun (m : Env.member) -> m.signature)
  | Trait_method (trait, name, _) ->
      Option.bind (Env.trait_info env trait) (fun (info : Env.trait_info) ->
          List.find_opt
            (fun (m : Env.trait_method) -> m.method_name = name)
            info.methods
          |> Option.map (fun (m : Env.trait_method) -> m.method_sig))
  | Operation _ -> None

(* For each parameter of what a call names, the receiver's first, whether it
   is non-escaping or a scope, or has the error type, from which no
   diagnostic arises (errors.error-type). *)
let passing env callee =
  match signature env callee with
  | Some s ->
      List.map2
        (fun passes (_, ty) ->
          passes || is_scope ty || Types.resolve ty = Types.Error)
        (Env.passing s) s.params
  | None -> []

let mem (v : Hir.var) = List.exists (fun (p : Hir.var) -> p.id = v.id)

(* The parameters of [through] that [e] names, at any depth. *)
let named ~through e =
  let found = ref [] in
  Walk.iter
    (fun (e : expr) ->
      match e.desc with
      | Local v when mem v through && not (mem v !found) -> found := v :: !found
      | _ -> ())
    e;
  !found

(* Every use of a parameter of [through] that keeps it, with the parameter:
   its occurrence, or the closure literal that names it. [allowed] says
   whether [e] is a callee, or an argument given to a non-escaping
   parameter. *)
let rec keeps env ~through ~allowed (e : expr) =
  let visit ~allowed = keeps env ~through ~allowed in
  match e.desc with
  | Local v when mem v through -> if allowed then [] else [ (v, e.loc) ]
  (* polymorphism.effects-and-escaping: a polymorphic value is used where it stands. *)
  | Instantiate (x, _) | Generalize (_, x) -> visit ~allowed x
  | Closure (_, _, body) ->
      (if allowed then []
       else List.map (fun v -> (v, e.loc)) (named ~through body))
      @ visit ~allowed:false body
  | Call (callee, _, args, _) ->
      let passing = passing env callee in
      List.concat
        (List.mapi
           (fun i (a : arg) ->
             let passes =
               a.mode <> Ast.Inout
               && Option.value (List.nth_opt passing i) ~default:false
             in
             visit ~allowed:passes a.value)
           args)
  | Call_value (f, args) ->
      visit ~allowed:true f
      @ List.concat_map (fun (a : arg) -> visit ~allowed:false a.value) args
  (* handlers.handler-types: installing a handler is a use it may have, as a call
     is. *)
  | With (h, _, _, b) ->
      visit ~allowed:true h
      @ List.concat_map (visit ~allowed:false) (Walk.block_exprs b)
  | _ -> List.concat_map (visit ~allowed:false) (Walk.children e)

(* Each parameter that escapes gets one error, at the first use in source
   order that keeps it. *)
(* tasks.scope-that-escapes: the scopes that a body names, which escape as
   non-escaping parameters do. *)
let scopes block =
  let found = ref [] in
  Walk.iter_block
    (fun (e : expr) ->
      match e.desc with
      | Local v when is_scope e.ty && not (mem v !found) -> found := v :: !found
      | _ -> ())
    block;
  List.rev !found

let message ~scopes (v : Hir.var) =
  if mem v scopes then
    Printf.sprintf
      "the scope `%s` is kept here, but it ends when `task.scope` returns: use \
       it only to start tasks"
      v.name
  else
    Printf.sprintf
      "`%s` is kept here, but its effects pass through to the caller: write \
       `escaping %s`"
      v.name v.name

let errors env ~file ~through block =
  let scopes = scopes block in
  let through = through @ List.filter (fun v -> not (mem v through)) scopes in
  let uses =
    List.concat_map (keeps env ~through ~allowed:false) (Walk.block_exprs block)
  in
  let first (v : Hir.var) =
    List.fold_left
      (fun best ((w : Hir.var), (loc : Ast.loc)) ->
        if w.id <> v.id then best
        else
          match best with
          | Some (b : Ast.loc) when (b.line, b.col) <= (loc.line, loc.col) ->
              best
          | _ -> Some loc)
      None uses
  in
  List.filter_map
    (fun (v : Hir.var) -> Option.map (fun loc -> (loc, v)) (first v))
    through
  |> List.sort compare
  |> List.map (fun ((loc : Ast.loc), (v : Hir.var)) ->
      Diagnostic.at ~file
        (if mem v scopes then Code.e0434 else Code.e0508)
        loc (message ~scopes v))
