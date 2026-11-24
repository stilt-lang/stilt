(* handlers.resume-at-most-once: an operation's body of a handler that takes control
   resumes at most once on each path: never in a loop or a closure literal,
   never twice in sequence, and never in a branch after another branch that
   resumed. *)

open Tast

let message =
  "this may resume a second time, but a handler resumes at most once on each \
   path, so that no continuation is copied"

(* Every [resume] in [e], outside the handler literals in it, whose own
   operations [errors] checks. *)
let rec resumes acc (e : expr) =
  match e.desc with
  | Resume x ->
      Option.fold ~none:(e.loc :: acc) ~some:(resumes (e.loc :: acc)) x
  | Handler _ -> acc
  | _ -> List.fold_left resumes acc (Walk.children e)

(* [flow report resumed e] follows [e] in evaluation order and tells whether
   a path through it may have resumed by its end, given [resumed] before it,
   reporting each [resume] that may run after another. A [return], [break],
   [continue] or [raise] ends its path. *)
let rec flow report resumed (e : expr) =
  let go = flow report in
  let seq r es = List.fold_left go r es in
  let block r b = seq r (Walk.block_exprs b) in
  match e.desc with
  | Resume x ->
      let r = seq resumed (Option.to_list x) in
      if r then report e.loc;
      true
  | Handler _ -> resumed
  | Closure _ | Loop _ | While _ | For _ ->
      (* handlers.resume-at-most-once: a [resume] in a loop or a closure literal may run twice. *)
      List.iter report (List.rev (resumes [] e));
      resumed
  | If (c, b, alt) | If_let (_, c, b, alt) ->
      let r = go resumed c in
      let taken = block r b in
      let other = Option.fold ~none:r ~some:(go r) alt in
      taken || other
  | Match (s, arms) | Try (s, Some { arms; _ }) ->
      let r = go resumed s in
      List.fold_left
        (fun any (a : arm) -> go (seq r (Option.to_list a.guard)) a.body || any)
        r arms
  | Else (a, b) | Binary ((And | Or), a, b) ->
      (* The right operand is followed whether or not the left one resumed, so
         that its [resume]s are reported. *)
      let r = go resumed a in
      let right = go r b in
      r || right
  | Return x ->
      ignore (seq resumed (Option.to_list x));
      false
  | Raise x ->
      ignore (go resumed x);
      false
  | Break | Continue -> false
  | _ -> seq resumed (Walk.children e)

(* The [resume]s of a body that may run a second time, in source order. *)
let errors ~file block =
  let found = ref [] in
  let report (loc : Ast.loc) =
    if not (List.mem loc !found) then found := loc :: !found
  in
  Walk.iter_block
    (fun (e : expr) ->
      match e.desc with
      | Handler { control = true; ops; _ } ->
          List.iter
            (fun (_, (op : expr)) ->
              match op.desc with
              | Closure (_, _, body) -> ignore (flow report false body)
              | _ -> ())
            ops
      | _ -> ())
    block;
  List.sort compare !found
  |> List.map (fun loc -> Diagnostic.at ~file Code.e0514 loc message)
