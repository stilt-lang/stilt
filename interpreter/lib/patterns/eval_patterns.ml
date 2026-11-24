(* The evaluation of patterns (patterns.match): the arms of a [match] or a [catch],
   tried in order, and whether a pattern matches a value, with the bindings
   it makes. Guards and constant patterns are expressions, which [expr]
   evaluates. *)

open Tast
open Value
open Eval_state
open Eval_types
open Eval_operators

type expr = Eval_state.t -> Eval_state.frame -> Tast.expr -> Value.value

let rec arms ~expr t fr arms v =
  let chosen (a : arm) =
    matches ~expr t fr a.pattern v (fun () ->
        match a.guard with Some g -> truth (expr t fr g) | None -> true)
  in
  match List.find_opt chosen arms with
  | Some a -> expr t fr a.body
  | None -> invalid_arg "Eval_exprs.arms: no arm matches"

and pattern ~expr t fr p v = matches ~expr t fr p v (fun () -> true)

(* Whether [p] matches [v] in a way that satisfies [k], which runs with each
   way's bindings in turn. The ways differ in the alternative each
   or-pattern takes, from left to right, so a guard is tried with each
   alternative that matches (patterns.guards). *)
and matches ~expr t fr (p : pattern) v k =
  match (p.pat, v) with
  | P_wild, _ -> k ()
  | P_bind var, _ ->
      Hashtbl.replace fr.locals var.id v;
      k ()
  | P_int text, Int x -> Int64.equal x (pattern_literal text) && k ()
  | P_str s, Str x -> String.equal s x && k ()
  | P_bool b, Bool x -> b = x && k ()
  | P_tuple ps, Tuple xs -> match_all ~expr t fr ps xs k
  | P_const c, _ -> same (expr t fr c) v && k ()
  | P_variant (item, ps), Variant (w, xs) ->
      item = w
      &&
      (* meta.fresh-types: a case of a shape binds its fresh types. *)
      (if Meta.is_meta item then Eval_meta.bind_case t fr p.pty item ps;
       match_all ~expr t fr ps xs k)
  | P_record fields, Record (_, xs) ->
      let field (f, _) = List.assoc f xs in
      match_all ~expr t fr (List.map snd fields) (List.map field fields) k
  | P_list (ps, rest), List xs ->
      let n = List.length ps and length = Vec.length xs in
      let fits =
        match rest with
        | Exact -> length = n
        | Rest | Rest_bind _ -> length >= n
      in
      fits
      && match_all ~expr t fr ps
           (Vec.to_list (Vec.sub xs 0 n))
           (fun () ->
             (match rest with
             | Rest_bind var ->
                 Hashtbl.replace fr.locals var.id (List (Vec.sub xs n length))
             | Exact | Rest -> ());
             k ())
  | P_or ps, _ -> List.exists (fun q -> matches ~expr t fr q v k) ps
  | _ -> false

and match_all ~expr t fr ps xs k =
  match (ps, xs) with
  | p :: ps, x :: xs ->
      matches ~expr t fr p x (fun () -> match_all ~expr t fr ps xs k)
  | _ -> k ()
