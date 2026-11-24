(* Matches: a value to match on, the patterns that cover it, and [match]
   expressions. *)

open Code
open Context
open Ty

let bind b ty =
  let v = { name = fresh b.p "m"; ty; mutable_ = false } in
  (v.name, [ v ])

(* The arms of a match on a variant type: a pattern for each variant, or for
   all but the last and a catch-all. *)
let variant_arms b cases =
  let r = b.p.r in
  let arm (case, payload) =
    let parts =
      List.map
        (fun t -> if Pick.chance r 0.3 then ("_", []) else bind b t)
        payload
    in
    if payload = [] then (case, [])
    else (call_text case (List.map fst parts), List.concat_map snd parts)
  in
  let arms = List.map arm cases in
  let n = List.length arms in
  if n > 1 && Pick.chance r 0.3 then
    List.filteri (fun i _ -> i < n - 1) arms @ [ ("_", []) ]
  else arms

let patterns expr b sc ~depth ty =
  let r = b.p.r in
  let guarded arms =
    match arms with
    | (pattern, bound) :: _ when Pick.chance r 0.3 ->
        let guard =
          Bools.cond expr b { sc with vars = bound @ sc.vars } ~depth
        in
        (pattern ^ " if " ^ guard.text, bound) :: arms
    | _ -> arms
  in
  let literals make =
    let values =
      List.sort_uniq compare (Pick.times (Pick.between r 1 3) make)
    in
    List.map (fun v -> (v, [])) values @ [ ("_", []) ]
  in
  match ty with
  | Named name -> (
      match decl b name with
      | Variants cases -> guarded (variant_arms b cases)
      | Record _ -> [ bind b ty ])
  | Option t ->
      let some, bound = bind b t in
      guarded [ ("Some(" ^ some ^ ")", bound); ("None", []) ]
  | Int k ->
      literals (fun () ->
          string_of_int
            (if signed k then Pick.between r (-2) 4 else Pick.between r 0 4))
  | Bool -> guarded [ ("true", []); ("false", []) ]
  | Str ->
      literals (fun () ->
          Printf.sprintf "\"%c\"" (Char.chr (Pick.between r 97 99)))
  | Tuple [ Int I64; Bool ] ->
      let n, bound = bind b (Int I64) in
      guarded
        [ ("(0, _)", []); ("(" ^ n ^ ", true)", bound); ("(_, false)", []) ]
  | _ -> [ bind b ty ]

(* A value to match on, and patterns that cover it, each with the variables
   it binds. A guarded arm, which covers nothing for exhaustiveness (patterns.guards),
   may come first. *)
let scrutinee expr b sc ~depth =
  let r = b.p.r in
  let variants =
    List.filter_map
      (fun (name, d) ->
        match d with
        | Variants _ when not (has_map b.p.decls (Named name)) ->
            Some (Named name)
        | _ -> None)
      b.p.decls
  in
  let ty =
    Pick.run r
      [
        ((if variants = [] then 0 else 4), fun () -> Pick.one r variants);
        (2, fun () -> Option (random_ty b.p ~maps:false 1));
        (2, fun () -> Int (Pick.one r int_kinds));
        (1, fun () -> Bool);
        (1, fun () -> Str);
        (1, fun () -> Tuple [ Int I64; Bool ]);
      ]
  in
  (expr b sc ~depth ~known:true ty, patterns expr b sc ~depth ty)

let match_expr expr b sc ~depth ~known ty =
  let d = depth - 1 in
  let s, arms = scrutinee expr b sc ~depth:d in
  let bodies =
    List.mapi
      (fun i (pattern, bound) ->
        let sc = { sc with vars = bound @ sc.vars } in
        pattern ^ " => " ^ (expr b sc ~depth:d ~known:(known && i = 0) ty).text)
      arms
  in
  compound ~known
    ("match " ^ head s.text ^ " { " ^ String.concat ", " bodies ^ " }")
