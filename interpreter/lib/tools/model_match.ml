open Model_json
open Model_types
open Model_forms

(* Whether a pattern holds a constant whose value is no literal the model's patterns
   write, which the export then compares in the guard. *)
let rec has_lifted cx (p : Tast.pattern) =
  match p.pat with
  | P_const c -> const_literal cx c = None
  | P_tuple ps | P_variant (_, ps) | P_list (ps, _) | P_or ps ->
      List.exists (has_lifted cx) ps
  | P_record fs -> List.exists (fun (_, p) -> has_lifted cx p) fs
  | _ -> false

(* patterns.constants: a constant in a pattern matches the values structurally equal to
   it. A constant whose value is a literal is a constant pattern of the model; any other
   is a fresh name in its place, and the comparison of that name with the constant in
   the guard. No constant's type writes its [Eq] (patterns.constants-with-written-eq),
   so [==] is the structural one. *)
let rec lift cx (p : Tast.pattern) =
  let many ps =
    let ps, gs = List.split (List.map (lift cx) ps) in
    (ps, List.concat gs)
  in
  match p.pat with
  | P_const c when const_literal cx c = None ->
      let v = { Hir.id = -1; name = temp "constant" p.ploc; loc = p.ploc } in
      let x = { Tast.desc = Local v; ty = p.pty; loc = p.ploc } in
      let eq =
        { Tast.desc = Binary (Eq, x, c); ty = prelude_ty "bool"; loc = p.ploc }
      in
      ({ p with pat = P_bind v }, [ eq ])
  | P_tuple ps ->
      let ps, gs = many ps in
      ({ p with pat = P_tuple ps }, gs)
  | P_variant (c, ps) ->
      let ps, gs = many ps in
      ({ p with pat = P_variant (c, ps) }, gs)
  | P_list (ps, rest) ->
      let ps, gs = many ps in
      ({ p with pat = P_list (ps, rest) }, gs)
  | P_record fs ->
      let ps, gs = many (List.map snd fs) in
      ({ p with pat = P_record (List.combine (List.map fst fs) ps) }, gs)
  | P_or _ when has_lifted cx p -> outside "a constant in a nested or-pattern"
  | _ -> (p, [])

(* The arm with the constants it can't write as patterns lifted into its guard,
   compared before the guard runs. *)
let lifted cx (a : Tast.arm) =
  let pattern, eqs = lift cx a.pattern in
  let both g h =
    { Tast.desc = Binary (And, g, h); ty = prelude_ty "bool"; loc = g.loc }
  in
  match (eqs, a.guard) with
  | [], _ -> a
  | e :: es, guard ->
      let eqs = List.fold_left both e es in
      {
        a with
        pattern;
        guard = Some (Option.fold ~none:eqs ~some:(both eqs) guard);
      }

(* The arms as the calculus writes them, each with its guard (patterns.guards). A
   top-level or-pattern whose constants are lifted tries its alternatives from left to
   right, each with the guard. *)
let arms ~expr cx arms =
  let rec compile = function
    | [] -> []
    | (a : Tast.arm) :: rest -> (
        match a.pattern.pat with
        | P_or ps when has_lifted cx a.pattern ->
            compile (List.map (fun p -> { a with pattern = p }) ps @ rest)
        | _ ->
            let a = lifted cx a in
            guarded_arm cx a.pattern (Option.map expr a.guard) (expr a.body)
            :: compile rest)
  in
  compile arms

let guarded ~expr cx t scrutinee a =
  tag "match" [ scrutinee; ty cx t; Arr (arms ~expr cx a) ]

let match_e ~expr cx (e : Tast.expr) (x : Tast.expr) a =
  guarded ~expr cx e.ty (expr x) a
