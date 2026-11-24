(* Staging annotations (meta.staging-annotations): the parts that a [comptime] marks as known
   at compile time are static expressions (meta.static-expressions), each reported once, at
   its first part that isn't static in evaluation order (E0349). *)

open Tast
module T = Types

(* The variables of a body, by id, as meta.static-expressions sorts them. *)
type scope = {
  static : (int, unit) Hashtbl.t;
      (* Those that an enclosing annotation, or a [let] from a static value,
         binds. *)
  params : (int, unit) Hashtbl.t; (* A function's or a closure's. *)
  vars : (int, unit) Hashtbl.t; (* Those that a [var] binds. *)
}

let add table ids = List.iter (fun id -> Hashtbl.replace table id ()) ids
let bound p = Modes_places.pattern_vars p

(* Why a local isn't static. *)
let local_reason sc (v : Hir.var) =
  if Hashtbl.mem sc.params v.id then
    Printf.sprintf "`%s` is a parameter, which is known only at run time" v.name
  else if Hashtbl.mem sc.vars v.id then
    Printf.sprintf "`%s` is a `var`, which may change" v.name
  else Printf.sprintf "`%s` is bound from a value known only at run time" v.name

(* Whether a call's row, its type parameters instantiated, is empty, so that
   it performs nothing (meta.static-expressions). Its implicit effects don't count. *)
let empty_row row =
  let r = T.row_contents row in
  (not r.io) && r.raise = None && r.effects = [] && T.params r = []

(* The forms that run code, which meta.not-static reports whole. *)
let code_form (e : expr) =
  match e.desc with
  | Block _ -> Some "a block"
  | If _ | If_let _ -> Some "an `if`"
  | Match _ -> Some "a `match`"
  | Loop _ | While _ | For _ -> Some "a loop"
  | Closure _ -> Some "a closure"
  | Try _ -> Some "a `try`"
  | Else _ -> Some "an `else`"
  | Comptime inner -> (
      match inner.desc with
      | Match _ -> Some "a `match`"
      | For _ -> Some "a loop"
      | _ -> Some "an `if`")
  | Raise _ | Return _ | Break | Continue | Hole | Handler _ | With _ | Resume _
  | When _ ->
      Some "this expression"
  | _ -> None

(* The first part of [e] that isn't static, in evaluation order, with why:
   the parts that an expression holds come before the expression. *)
let rec first sc (e : expr) =
  let parts es = List.find_map (first sc) es in
  match (code_form e, e.desc) with
  | Some what, _ -> Some (e.loc, what ^ " runs code, so it isn't static")
  | None, (Int _ | Float _ | Str _ | Bool _ | Error) -> None
  | None, (Constant _ | Member_constant _ | Trait_constant _ | Value_param _) ->
      None
  (* meta.static-reflection: a type's shape, its name and a bound test. *)
  | None, Reflect _ -> None
  | None, Local v ->
      if Hashtbl.mem sc.static v.id then None
      else Some (e.loc, local_reason sc v)
  | None, Interpolated segments ->
      parts
        (List.filter_map
           (function Splice (x, _) -> Some x | Text _ -> None)
           segments)
  | None, (Tuple es | List es | Construct (_, _, es)) -> parts es
  | None, Record (_, _, fields) -> parts (List.map snd fields)
  | None, Update (base, fields) -> parts (base :: List.map snd fields)
  | None, Spread s -> first sc s.body
  | None, (Field (x, _) | Tuple_field (x, _) | Unary (_, x)) -> first sc x
  | None, (Index (a, b) | Binary (_, a, b)) -> parts [ a; b ]
  | None, (Generalize (_, x) | Instantiate (x, _)) -> first sc x
  | None, (Call (_, _, args, row) | Project (_, _, args, row)) -> (
      match parts (List.map (fun (a : arg) -> a.value) args) with
      | Some found -> Some found
      | None when empty_row row -> None
      | None ->
          Some
            ( e.loc,
              "this call performs the effects of its row, so it isn't static" ))
  | None, Call_value (f, args) -> (
      match parts (f :: List.map (fun (a : arg) -> a.value) args) with
      | Some found -> Some found
      | None ->
          Some
            ( e.loc,
              "this call goes through a function value, so it isn't static" ))
  | None, (Callee _ | Constructor _) ->
      Some (e.loc, "a function value isn't static")
  | None, _ -> Some (e.loc, "this expression isn't static")

(* An annotated part, E0349 at its first part that isn't static. *)
let part sc report (e : expr) =
  Option.iter (fun (loc, why) -> report loc why) (first sc e)

let iterable sc report = function
  | Iter x -> part sc report x
  | Range (a, b, _) -> (
      match List.find_map (first sc) [ a; b ] with
      | Some (loc, why) -> report loc why
      | None -> ())

(* meta.static-expressions: the condition of every [if] and the scrutinee of every [if let]
   of a chain, whose patterns bind static variables in their branches. *)
let rec chain sc report (e : expr) =
  match e.desc with
  | If (c, _, alt) ->
      part sc report c;
      Option.iter (chain sc report) alt
  | If_let (p, s, _, alt) ->
      part sc report s;
      add sc.static (bound p);
      Option.iter (chain sc report) alt
  | _ -> ()

(* The parts of an annotation, which the patterns of its form make static
   in the code they bind for (meta.static-expressions and meta.staged-loops). *)
let annotation sc report (form : expr) =
  match form.desc with
  | For (p, it, _) ->
      iterable sc report it;
      add sc.static (bound p)
  | If _ | If_let _ -> chain sc report form
  | Match (s, arms) ->
      part sc report s;
      List.iter
        (fun (a : arm) ->
          add sc.static (bound a.pattern);
          Option.iter (part sc report) a.guard)
        arms
  | _ -> ()

(* The bindings that a body makes, as meta.static-expressions reads them: a [let] from a
   static value binds static variables. *)
let statement sc (s : stmt) =
  match s.stmt with
  | Let { pattern; value; otherwise = None; _ } when first sc value = None ->
      add sc.static (bound pattern)
  | Var b -> add sc.vars (bound b.pattern)
  | Let _ | Assign _ | Assert _ | Yield _ | Expr _ -> ()

let errors ~file ~params block =
  let sc =
    {
      static = Hashtbl.create 16;
      params = Hashtbl.create 16;
      vars = Hashtbl.create 16;
    }
  in
  add sc.params (List.map (fun (_, (v : Hir.var)) -> v.id) params);
  let found = ref [] in
  let report loc why =
    found := Diagnostic.at ~file Code.e0349 loc why :: !found
  in
  Walk.iter_block ~stmt:(statement sc)
    (fun (e : expr) ->
      match e.desc with
      | Comptime form -> annotation sc report form
      | Closure (ps, _, _) -> add sc.params (List.concat_map bound ps)
      | _ -> ())
    block;
  List.rev !found
