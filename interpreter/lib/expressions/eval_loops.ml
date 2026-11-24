(* The evaluation of loops (expressions.loops) and of the iterables
   of [for] (expressions.for-iterables; views.for-over-view): [block] runs a loop's body, and
   [expr] evaluates an iterable or a range's bounds. *)

open Tast
open Value
open Eval_state
open Eval_types
open Eval_operators

(* Runs a loop's body while [more ()] holds, until it breaks. The head of a
   [while], like the iterable of a [for], is outside the body, so a [break]
   or [continue] there acts on an enclosing loop (expressions.loops and expressions.break-and-continue). *)
let rec repeat ~block t fr b more =
  if more () && turn ~block t fr b then repeat ~block t fr b more

(* Runs a loop's body once, and tells whether the loop goes on. *)
and turn ~block t fr b =
  check_memory ();
  (* macros.step-limits *)
  step ();
  match block t fr b with
  | _ -> true
  | exception Continue -> true
  | exception Break -> false

let iterate ~expr t fr (iterable : iterable) each =
  match iterable with
  | Iter source -> (
      match Eval_windows.thaw t fr (expr t fr source) with
      | List xs -> ignore (List.for_all each (Vec.to_list xs))
      | Map d ->
          ignore
            (List.for_all
               (fun (k, v) -> each (Tuple [ k; v ]))
               (Dict.entries d))
      (* views.for-over-view: a view of a list is the part it views, and an
         iterator gives each element only once the body has run on the one
         before. *)
      | Iter it -> Eval_iters.iterate t fr source.loc it each
      | _ -> invalid_arg "Eval_exprs.iterate")
  | Range (a, z, kind) -> (
      let k =
        match numeric (concrete fr a.ty) with
        | Integer k -> k
        | _ -> invalid_arg "Eval_exprs.iterate: range"
      in
      let first = expr t fr a in
      let last = expr t fr z in
      match (first, last) with
      | Int first, Int last ->
          (* Stops at the last value without stepping past it, since it may be
             the type's maximum. *)
          let rec from i =
            let c = Ints.compare k i last in
            if
              (c < 0 || (c = 0 && kind = Ast.Inclusive))
              && each (Int i) && c < 0
            then from (Int64.succ i)
          in
          from first
      | _ -> invalid_arg "Eval_exprs.iterate: range bounds")
