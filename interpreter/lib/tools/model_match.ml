open Model_json
open Model_types
open Model_forms

let rec has_or (p : Tast.pattern) =
  match p.pat with
  | P_or _ -> true
  | P_tuple ps | P_variant (_, ps) | P_list (ps, _) -> List.exists has_or ps
  | P_record fs -> List.exists (fun (_, p) -> has_or p) fs
  | _ -> false

let rec has_const (p : Tast.pattern) =
  match p.pat with
  | P_const _ -> true
  | P_tuple ps | P_variant (_, ps) | P_list (ps, _) | P_or ps ->
      List.exists has_const ps
  | P_record fs -> List.exists (fun (_, p) -> has_const p) fs
  | _ -> false

(* patterns.constants: a constant in a pattern matches the values structurally equal to
   it, so a pattern with constants is the pattern with a fresh name in each one's place,
   and the comparisons of those names with the constants, a guard. No constant's type
   writes its [Eq] (patterns.constants-with-written-eq), so [==] is the structural one. *)
let rec lift (p : Tast.pattern) =
  let many ps =
    let ps, gs = List.split (List.map lift ps) in
    (ps, List.concat gs)
  in
  match p.pat with
  | P_const c ->
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
  | P_or _ when has_const p -> outside "a constant in a nested or-pattern"
  | _ -> (p, [])

(* The arm with its constants lifted into its guard, compared before the guard runs. *)
let lifted (a : Tast.arm) =
  let pattern, eqs = lift a.pattern in
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

(* [p if g => a] followed by [rest] is [p => if g { a } else { match on the
   arms of [rest] }], then [rest]: an arm with a guard takes no part in
   exhaustiveness, so [rest] alone covers every value (patterns.guards). A
   top-level or-pattern with a guard tries its alternatives from left to right,
   each with the guard. *)
let guarded ~expr cx t scrutinee arms =
  let rec compile = function
    | [] -> []
    | (a : Tast.arm) :: rest -> (
        match (a.guard, a.pattern.pat) with
        | _, P_or ps when a.guard <> None || has_const a.pattern ->
            compile (List.map (fun p -> { a with pattern = p }) ps @ rest)
        | None, _ when has_const a.pattern -> compile (lifted a :: rest)
        | None, _ -> arm cx a.pattern (expr a.body) :: compile rest
        | Some _, _ when has_const a.pattern -> compile (lifted a :: rest)
        | Some g, _ ->
            if has_or a.pattern then outside "a guard on a nested or-pattern";
            let others =
              tag "match" [ scrutinee; ty cx t; Arr (compile rest) ]
            in
            let body = tag "if" [ expr g; ty cx t; expr a.body; others ] in
            arm cx a.pattern body :: compile rest)
  in
  tag "match" [ scrutinee; ty cx t; Arr (compile arms) ]

let match_e ~expr cx (e : Tast.expr) (x : Tast.expr) arms =
  let plain (a : Tast.arm) = a.guard = None && not (has_const a.pattern) in
  if List.for_all plain arms then guarded ~expr cx e.ty (expr x) arms
  else
    let v = temp "match" e.loc in
    tag "letIn"
      [ Str v; ty cx x.ty; expr x; guarded ~expr cx e.ty (var_e v) arms ]
