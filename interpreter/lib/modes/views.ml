(* Views in a body: the views it makes of what can't be viewed
   (E0420, views.viewable-types), the views it stores (E0421, views.view-types), and the views that
   outlive their sources (E0422, views.escaping, which Views_escapes checks). The
   reads that views make, and E0423, are the exclusivity pass's (Modes). *)

open Tast
module T = Types
module V = Views_types
module S = Views_sources

let can't_view t =
  Printf.sprintf "`%s` can't be viewed: a view is of a `str` or a `List`"
    (Types_show.to_string t)

(* views.viewable-types: [View.of] or [View.all] of a type that can't be viewed, at its
   argument, or at the function where it is a value. A type that is an error,
   or that inference left unsettled because of one, was reported where the
   error is. *)
let inferred report (e : expr) =
  let view_maker = function
    | Member ({ home = "std.view"; name = "View" }, ("of" | "all")) -> true
    | _ -> false
  in
  let unviewable t =
    match T.resolve t with T.Error | Var _ -> false | _ -> not (V.viewable t)
  in
  match e.desc with
  | Call (c, t :: _, a :: _, _) when view_maker c && unviewable t ->
      report Code.e0420 a.value.loc (can't_view t)
  | Callee (c, t :: _) when view_maker c && unviewable t ->
      report Code.e0420 e.loc (can't_view t)
  | _ -> ()

(* views.view-types: an expression that builds a value that stores a view, from a view
   or a closure that captures one, where no part of it stores one already,
   as [[v]], [(v, 1)] or a [collect] of views do. A literal stores a closure
   that captures a view, which its type doesn't show (views.view-types). [Option]
   holds views. *)
let stored t report (e : expr) =
  let parts =
    List.filter_map
      (function Walk.Expr p -> Some p | Block _ -> None)
      (Walk.parts e)
  in
  let literal =
    match e.desc with
    | List _ | Tuple _ | Record _ -> true
    | Construct (item, _, _) -> item <> T.prelude_item "Some"
    | _ -> false
  in
  (* shared.tasks-and-modes: a view put in a [Shared<T>] is E0432, which a demand
     reports. *)
  let call =
    match e.desc with
    | Call (c, _, _, _) -> not (Demands.demanded c 0)
    | Project _ | Call_value _ -> true
    | _ -> false
  in
  if
    (literal || (call && V.stores e.ty))
    && List.exists (S.carries t) parts
    && not (List.exists (fun (p : expr) -> V.stores p.ty) parts)
  then
    report Code.e0421 e.loc
      "this stores a view, which can't be stored: a view lives only in a \
       local, a parameter, a result or a closure"

(* views.viewable-types and views.view-types: the types written in a body, for its bindings and its
   closures' parameters. *)
let written report (e : expr) =
  match e.desc with
  | Closure (_, written, _) ->
      List.iter (V.written report ~stored:false) written
  | _ -> ()

let written_binding report (s : stmt) =
  match s.stmt with
  | Let b | Var b -> Option.iter (V.written report ~stored:false) b.written
  | Assign _ | Assert _ | Yield _ | Expr _ -> ()

let errors env ~file ~params block =
  let found = ref [] in
  let report code loc message =
    found := Diagnostic.at ~file code loc message :: !found
  in
  let t = S.collect block in
  Walk.iter_block
    ~stmt:(fun s ->
      written_binding report s;
      Views_writes.stmt t report s;
      Views_escapes.stmt t report ~params s)
    (fun e ->
      inferred report e;
      stored t report e;
      written report e;
      Views_escapes.expr env t report e)
    block;
  Views_escapes.body t report ~params block;
  (* One error at an expression that several rules reject: the first, which
     is that of the innermost scope it leaves. *)
  let first (seen, kept) (d : Diagnostic.t) =
    let key = (d.code, d.line, d.col) in
    if List.mem key seen then (seen, kept) else (key :: seen, d :: kept)
  in
  List.rev (snd (List.fold_left first ([], []) (List.rev !found)))
