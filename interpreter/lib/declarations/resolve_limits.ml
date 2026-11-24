(* The [without] clauses of module headers and functions (program.header-limits;
   declarations.limits). *)

open Hir
open Resolve_context

let name = Capability.limit_name

(* The limits of a clause, each named once: one named again is reported at
   its second occurrence, through [report], and ignored. *)
let distinct report (w : Ast.without) =
  List.fold_left
    (fun kept (l : limit node) ->
      if List.exists (fun (k : limit node) -> k.desc = l.desc) kept then (
        report l.loc (name l.desc);
        kept)
      else kept @ [ l ])
    [] w.desc

let of_header st ~file = function
  | [] -> []
  | (first : Ast.without) :: rest ->
      List.iter
        (fun (w : Ast.without) ->
          report st ~file Code.e0202 w.loc
            "this header already has a `without`, which names every limit")
        rest;
      distinct
        (fun loc limit ->
          report st ~file Code.e0202 loc
            "`%s` is already named in this `without`" limit)
        first

let of_fn ctx = function
  | None -> []
  | Some w ->
      distinct
        (fun loc limit ->
          errorf ctx Code.e0202 loc "`%s` is already named in this `without`"
            limit)
        w
