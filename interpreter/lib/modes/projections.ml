(* Yielding exactly once (projections.once-on-every-path): every path through a
   projection's body from its start to its end or to a [return] runs one
   [yield], and a path that ends by raising or panicking runs at most one.
   The check is syntactic: it follows the counts of yields that each path
   can have reached, 0, 1 or more, through the arms of branches, and reports
   E0424 at a [yield] inside a loop or the operand of a [try] with arms,
   which could run more than once or not at all, at the second [yield] of a
   path, and at the end of the body or the [return] that a path reaches
   without one. *)

open Tast

(* The counts that the paths reaching a point have: 0, 1 or 2, which stands
   for more. *)
type counts = int list

let union a b = List.sort_uniq compare (a @ b)

(* An expression that ends its paths: one of type [Never], or a hole, which
   panics when reached, so its path runs at most one [yield] (projections.once-on-every-path). *)
let never (e : expr) =
  Types.resolve e.ty = Types.never
  || match e.desc with Hole -> true | _ -> false

type ctx = {
  report : Code.t -> Ast.loc -> string -> unit;
  inside : string option;
      (** The construct a [yield] here would be inside, which could run it more
          than once or not at all: a loop, or a [try] with arms. *)
}

(* The counts after an expression, which holds yields only in its blocks and
   arms; an expression of type [Never] ends its paths. *)
let rec expr ctx counts (e : expr) : counts =
  let after =
    match e.desc with
    | Block b -> block ctx counts b
    | If (_, b, alt) ->
        union (block ctx counts b)
          (match alt with Some x -> expr ctx counts x | None -> counts)
    | If_let (_, _, b, alt) ->
        union (block ctx counts b)
          (match alt with Some x -> expr ctx counts x | None -> counts)
    | Match (_, arms) ->
        List.fold_left
          (fun acc (a : arm) -> union acc (expr ctx counts a.body))
          [] arms
    | Try (x, c) ->
        let inside =
          if c = None then ctx.inside else Some "a `try` with arms"
        in
        let after = expr { ctx with inside } counts x in
        List.fold_left
          (fun acc (a : arm) -> union acc (expr ctx after a.body))
          after (Walk.catch_arms c)
    | Loop b | While (_, b) | For (_, _, b) ->
        let inside = Some "a loop" in
        let after = block { ctx with inside } counts b in
        (* A yield in the body, reported there, counts as the one yield of
           the paths through the loop. *)
        if after <> counts then List.map (fun c -> min 2 (c + 1)) counts
        else counts
    | Return _ ->
        if List.mem 0 counts then
          ctx.report Code.e0424 e.loc
            "this `return` ends a path through the projection that hasn't \
             yielded: every path yields exactly once";
        counts
    | Closure _ -> counts
    (* meta.erasure: an annotated form's paths are the form's. *)
    | Comptime x -> expr ctx counts x
    | _ -> counts
  in
  if never e then [] else after

and stmt ctx counts (s : stmt) : counts =
  match s.stmt with
  | Yield _ ->
      (match ctx.inside with
      | Some what ->
          ctx.report Code.e0424 s.at
            (Printf.sprintf
               "this `yield` is inside %s, so it could run more than once or \
                not at all: a projection yields exactly once"
               what)
      | None -> ());
      if List.mem 1 counts || List.mem 2 counts then
        ctx.report Code.e0424 s.at
          "this path through the projection has yielded already: a projection \
           yields exactly once";
      List.map (fun c -> min 2 (c + 1)) counts
  | Let b | Var b ->
      let counts = expr ctx counts b.value in
      Option.fold ~none:counts ~some:(expr ctx counts) b.otherwise
  | Assign (_, p, v) -> expr ctx (expr ctx counts p) v
  | Assert e | Expr e -> expr ctx counts e

and block ctx counts b = List.fold_left (stmt ctx) counts b

(* projections.once-on-every-path *)
let errors ~file ~at body =
  let found = ref [] in
  let report code loc message =
    found := Diagnostic.at ~file code loc message :: !found
  in
  let ctx = { report; inside = None } in
  let counts = block ctx [ 0 ] body in
  if List.mem 0 counts then
    report Code.e0424 at
      "a path through the projection reaches its end without a `yield`: every \
       path yields exactly once";
  List.rev !found
