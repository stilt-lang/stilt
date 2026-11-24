(* The evaluation of interpolated strings (lexical.interpolation; std.width-fill-and-alignment): each splice is shown, with its format spec applied. [expr]
   evaluates a splice. *)

open Tast
open Value
open Eval_state
open Eval_types
open Eval_traits

let rec interpolated ~expr t fr segments =
  let parts = List.map (segment ~expr t fr) segments in
  reserve (List.fold_left (fun n p -> n + String.length p) 0 parts);
  Str (String.concat "" parts)

and segment ~expr t fr = function
  | Text s -> s
  | Splice (x, spec) -> (
      let v = expr t fr x in
      let ty = concrete fr x.ty in
      let shown = show t fr x.loc "show" ty v in
      match spec with
      | None -> shown
      | Some spec ->
          (* std.width-fill-and-alignment: a number where the splice is written, not where
             its type parameter is instantiated. *)
          let number : Format_spec.number =
            match (numeric x.ty, v) with
            | Integer k, Int a -> Int (k, a)
            | Floating f32, Float a -> Float (f32, a)
            | _ -> Not_a_number
          in
          Format_spec.apply (Option.get (Format_spec.parse spec)) number shown)
