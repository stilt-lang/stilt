(* Counting loops and shrinking recursion (facts.counting-loops and facts.shrinking-recursion), and what
   each needs when it doesn't hold (facts.closest-rule). *)

open Tast

(* The results of the rules, whose constructors [Tast]'s [Error] would hide. *)
type ('a, 'e) outcome = ('a, 'e) result = Ok of 'a | Error of 'e

module C = Accept_code
module W = Accept_walk
module S = Accept_signs
module X = Accept_text
module R = Accept_rules

let reader (cx : R.cx) = cx.w.reader

(* The counter a side of the comparison names: a [var] of an integer type of
   the loop's body. *)
let counter (cx : R.cx) (l : W.looped) e =
  match C.name (reader cx) e with
  | Some v -> (
      match Hashtbl.find_opt cx.w.decls v.id with
      | Some (body, Var_init _) when body = l.lbody -> Some v
      | _ -> None)
  | None -> None

(* Whether the bound is made of literals, constants, names of bindings that
   the loop doesn't write, and lengths of places whose length it doesn't
   change, by [+], [-] and [*]; or where the loop changes it. *)
let rec bound (cx : R.cx) (l : W.looped) (e : expr) =
  let r = reader cx in
  let writes f =
    match W.first (W.in_span cx.w l.lbody l.lspan) f with
    | Some line -> Error (Some line)
    | None -> Ok ()
  in
  match (C.binding r e, C.len_of r e) with
  | Some v, _ -> writes (fun x -> x.root = v.id)
  | None, Some p -> writes (fun x -> W.changes x p)
  | None, None -> (
      match e.desc with
      | Int _ | Constant _ | Member_constant _ -> Ok ()
      | Unary (Neg, { desc = Int _; _ }) -> Ok ()
      | Binary ((Add | Sub | Mul), a, b) -> (
          match (bound cx l a, bound cx l b) with
          | Error (Some x), Error (Some y) -> Error (Some (min x y))
          | Error None, _ | _, Error None -> Error None
          | (Error _ as e), Ok () | Ok (), (Error _ as e) -> e
          | Ok (), Ok () -> Ok ())
      | _ -> Error None)

(* The first statement of the loop's own block that steps the counter, with
   its place among the block's statements and [s]. *)
let step (cx : R.cx) (l : W.looped) (v : Hir.var) grows =
  let op : Ast.binary = if grows then Add else Sub in
  let rec find i = function
    | [] -> None
    | ({ stmt = Assign (Some o, ({ desc = Local x; _ } as place), s); _ } :
        stmt)
      :: _
      when o = op && x.id = v.id && S.positive cx.signs s l.lbody ->
        Some (i, s, place)
    | _ :: rest -> find (i + 1) rest
  in
  find 0 l.block

(* The line of the first [continue] of a loop among [stmts], outside the loops
   and closure literals inside them. *)
let rec continues stmts =
  List.fold_left
    (fun acc s ->
      List.fold_left
        (fun acc e -> earliest acc (continue_in e))
        acc (Walk.stmt_exprs s))
    None stmts

and continue_in (e : expr) =
  match e.desc with
  | Continue -> Some e.loc.line
  | While _ | Loop _ | For _ | Closure _ -> None
  | _ ->
      List.fold_left
        (fun acc part ->
          earliest acc
            (match part with
            | Walk.Expr x -> continue_in x
            | Walk.Block b -> continues b))
        None (Walk.parts e)

and earliest a b =
  match (a, b) with
  | Some x, Some y -> Some (min x y)
  | Some _, None -> a
  | None, _ -> b

let counts (cx : R.cx) (l : W.looped) (v : Hir.var) b grows =
  match bound cx l b with
  | Error line -> Error (1, X.loop_bound line)
  | Ok () -> (
      match step cx l v grows with
      | None -> Error (2, X.loop_step v grows)
      | Some (i, s, place) -> (
          let before = List.filteri (fun j _ -> j < i) l.block in
          match continues before with
          | Some line -> Error (3, X.loop_continue cx.env v grows s line)
          | None -> (
              let elsewhere =
                W.first (W.in_span cx.w l.lbody l.lspan) (fun x ->
                    x.root = v.id && x.place != place)
              in
              match elsewhere with
              | Some line -> Error (4, X.loop_writes v line)
              | None -> Ok ())))

(* facts.counting-loops: whether the loop counts toward its bound, or what the counting
   loop needs. Of the two sides that may be its counter, the one whose first
   unmet condition comes latest is the closest, the left one first. *)
let counting (cx : R.cx) (l : W.looped) =
  let rec head (e : expr) =
    match e.desc with Binary (And, a, _) -> head a | _ -> e
  in
  match Option.map head l.cond with
  | Some { desc = Binary (((Lt | Le | Gt | Ge) as op), a, b); _ } -> (
      let grows = op = Lt || op = Le in
      let tries =
        List.filter_map
          (fun (v, bound, grows) ->
            Option.map (fun v -> counts cx l v bound grows) (counter cx l v))
          [ (a, b, grows); (b, a, not grows) ]
      in
      if List.mem (Ok ()) tries then Ok ()
      else
        let best =
          List.fold_left
            (fun acc t ->
              match (acc, t) with
              | None, Error e -> Some e
              | Some (s, _), Error (s', e) when s' > s -> Some (s', e)
              | _ -> acc)
            None tries
        in
        match best with
        | Some (_, need) -> Error need
        | None -> Error X.loop_var)
  | _ -> Error X.loop_comparison

(* facts.shrinking-recursion: whether every self-call passes [p - s] at [p]'s place, or every
   one [p + s], with [s] known positive: whether [p] falls. *)
let moves (cx : R.cx) calls i (p : Hir.var) =
  List.fold_left
    (fun acc ((call : W.pending), (args : arg list)) ->
      match (acc, List.nth_opt args i) with
      | ( Some falls,
          Some { value = { desc = Binary (((Add | Sub) as op), a, s); _ }; _ } )
        when (match a.desc with Local v -> v.id = p.id | _ -> false)
             && S.positive cx.signs s call.pbody ->
          let this = op = Sub in
          if falls = None || falls = Some this then Some (Some this) else None
      | _ -> None)
    (Some None) calls
  |> Option.join

(* Whether a test that guards the call bounds [p] from below where it falls,
   and from above where it grows, by a literal, a constant of facts.terms or
   another [let] parameter that every self-call passes unchanged. *)
let bounded (cx : R.cx) (call : W.pending) (p : Hir.var) falls calls params =
  let ops : C.cmp list = if falls then [ Gt; Ge ] else [ Lt; Le ] in
  let unchanged q =
    q <> p.id
    && List.exists
         (fun (j, (x : Hir.var)) ->
           x.id = q
           && List.for_all
                (fun (_, (args : arg list)) ->
                  match List.nth_opt args j with
                  | Some { value = { desc = Local y; _ }; _ } -> y.id = q
                  | _ -> false)
                calls)
         params
  in
  let valid : C.term -> bool = function
    | Num _ -> true
    | Name q -> unchanged q
    | _ -> false
  in
  List.exists
    (fun f ->
      List.exists
        (fun (a : C.atom) ->
          match a with
          | Cmp (x, op, y) ->
              (x = Name p.id && List.mem op ops && valid y)
              || (y = Name p.id && List.mem (C.mirrored op) ops && valid x)
          | _ -> false)
        (Dynarray.get cx.w.frames f).atoms)
    call.frames

let shrinks (cx : R.cx) params =
  let calls =
    List.filter_map
      (fun (p : W.pending) ->
        match p.op with Self_call args -> Some (p, args) | _ -> None)
      cx.w.pending
  in
  if calls = [] then None
  else
    let candidates =
      List.filter_map
        (fun (i, (p : Hir.var)) ->
          Option.map (fun falls -> (p, falls)) (moves cx calls i p))
        params
    in
    let unbounded (p, falls) =
      List.fold_left
        (fun acc ((c : W.pending), _) ->
          if bounded cx c p falls calls params then acc
          else earliest acc (Some c.node.loc.line))
        None calls
    in
    match candidates with
    | [] -> Some (R.Unproved X.shrink_form)
    | (p, falls) :: _ ->
        if List.exists (fun c -> unbounded c = None) candidates then
          Some (R.Proved Shrinking_recursion)
        else
          let line = Option.value (unbounded (p, falls)) ~default:0 in
          Some (R.Unproved (X.shrink_test p falls line))
