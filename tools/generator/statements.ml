(* Statements, and the blocks they make. A block's bindings end with it, and
   every loop runs a bounded number of times. *)

open Code
open Context
open Ty
open Expr

let binding b sc ~depth ~mutable_ =
  let ty = random_ty b.p 2 in
  let name = fresh b.p "v" in
  let e = expr b sc ~depth ~known:false ty in
  let keyword = if mutable_ then "var " else "let " in
  let text =
    if e.known && Pick.chance b.p.r 0.5 then keyword ^ name ^ " = " ^ e.text
    else keyword ^ name ^ ": " ^ to_string ty ^ " = " ^ e.text
  in
  (declare sc name ty ~mutable_, line text)

(* A let-else, whose [else] leaves the block (patterns.let-else). *)
let let_else b sc ~depth =
  let r = b.p.r in
  let d = depth - 1 in
  let leave =
    match sc.returns with
    | _ when sc.loop && Pick.chance r 0.6 -> Pick.one r [ "continue"; "break" ]
    | Some Unit | None -> "return"
    | Some ty -> "return " ^ (expr b sc ~depth:d ~known:false ty).text
  in
  let t = random_ty b.p ~maps:false 1 in
  let y = fresh b.p "y" in
  let pattern, value, sc' =
    if Pick.chance r 0.75 then
      ( "Some(" ^ y ^ ")",
        expr b sc ~depth:d ~known:true (Option t),
        declare sc y t ~mutable_:false )
    else
      let rest = fresh b.p "rest" in
      ( Printf.sprintf "[%s, ..%s]" y rest,
        expr b sc ~depth:d ~known:true (List t),
        declare (declare sc y t ~mutable_:false) rest (List t) ~mutable_:false
      )
  in
  ( sc',
    line
      (Printf.sprintf "let %s = %s else { %s }" pattern (operand value) leave)
  )

(* The statements that print, or that leave the code when a condition holds:
   a raise, a [break] or [continue], or a [return]. Each comes with its weight
   and the scope after it, which is [sc]. *)
let effects b sc ~depth =
  let r = b.p.r in
  let d = depth - 1 in
  let guarded text =
    line ("if " ^ head (cond b sc ~depth:d).text ^ " { " ^ text ^ " }")
  in
  [
    ( (if sc.io then 4 else 0),
      fun () ->
        (sc, line ("print(" ^ (expr b sc ~depth ~known:false Str).text ^ ")"))
    );
    ( (if sc.io then 1 else 0),
      fun () -> (sc, line ("eprint(" ^ (interpolation b sc ~depth:d).text ^ ")"))
    );
    ( (if sc.may_raise then 1 else 0),
      fun () ->
        let case, payload = Pick.one r b.p.fault_variants in
        let args =
          List.map (fun t -> (expr b sc ~depth:d ~known:false t).text) payload
        in
        ( sc,
          guarded ("raise " ^ if args = [] then case else call_text case args)
        ) );
    ( (if sc.loop then 1 else 0),
      fun () -> (sc, guarded (Pick.one r [ "break"; "continue" ])) );
    ( (if Option.is_some sc.returns then 1 else 0),
      fun () ->
        let value =
          match sc.returns with
          | Some Unit | None -> ""
          | Some ty -> " " ^ (expr b sc ~depth:d ~known:false ty).text
        in
        (sc, guarded ("return" ^ value)) );
  ]

let rec stmts b sc ~depth n =
  if n <= 0 then (sc, [])
  else
    let sc, first = stmt b sc ~depth in
    let sc, rest = stmts b sc ~depth (n - 1) in
    (sc, first @ rest)

(* The statements of a block, whose bindings end with it. *)
and block b sc ~depth = snd (stmts b sc ~depth (Pick.between b.p.r 1 4))

and stmt b sc ~depth =
  spend b sc 1;
  Pick.run b.p.r
    ([
       (6, fun () -> binding b sc ~depth ~mutable_:false);
       (4, fun () -> binding b sc ~depth ~mutable_:true);
     ]
    @ Changes.changes b sc ~depth
    @ effects b sc ~depth @ nested b sc ~depth)

(* The statements that nest code, which the depth and the budget must allow:
   a let-else, and the statements that hold blocks. *)
and nested b sc ~depth =
  let deeper = depth > 0 && affordable b sc 8 in
  [
    ((if deeper then 2 else 0), fun () -> let_else b sc ~depth);
    ((if deeper then 3 else 0), fun () -> (sc, if_stmt b sc ~depth));
    ((if deeper then 2 else 0), fun () -> (sc, for_each b sc ~depth));
    ((if deeper then 2 else 0), fun () -> (sc, for_range b sc ~depth));
    ((if deeper then 1 else 0), fun () -> (sc, counted_loop b sc ~depth));
    ((if deeper then 1 else 0), fun () -> (sc, match_stmt b sc ~depth));
  ]

and if_stmt b sc ~depth =
  let d = depth - 1 in
  let opening = "if " ^ head (cond b sc ~depth:d).text ^ " {" in
  let then_ = block b sc ~depth:d in
  if Pick.chance b.p.r 0.5 then block_lines opening then_ "}"
  else
    let else_ = block b sc ~depth:d in
    ((0, opening) :: nest then_)
    @ ((0, "} else {") :: nest else_)
    @ [ (0, "}") ]

(* A [for] over a list or a map. A variable it iterates can't change in its
   body (modes.law), and any other list is cut to four elements. *)
and for_each b sc ~depth =
  let r = b.p.r in
  let d = depth - 1 in
  let iterable =
    List.filter
      (fun v -> match v.ty with List _ | Map _ -> true | _ -> false)
      sc.vars
  in
  let source, elem, frozen =
    match iterable with
    | _ :: _ when Pick.chance r 0.5 ->
        let v = Pick.one r iterable in
        let elem =
          match v.ty with
          | List t -> t
          | Map (k, t) -> Tuple [ k; t ]
          | _ -> invalid_arg "Statements.for_each"
        in
        (v.name, elem, [ v.name ])
    | _ ->
        let t = random_ty b.p ~maps:false 1 in
        let xs = expr b sc ~depth:d ~known:true (List t) in
        ( (method_on xs "take" [ string_of_int (Pick.between r 1 4) ]).text,
          t,
          [] )
  in
  let pattern, bound =
    match elem with
    | Tuple ts when Pick.chance r 0.6 ->
        let vars =
          List.map
            (fun t -> { name = fresh b.p "x"; ty = t; mutable_ = false })
            ts
        in
        ("(" ^ String.concat ", " (List.map (fun v -> v.name) vars) ^ ")", vars)
    | _ ->
        let v = { name = fresh b.p "x"; ty = elem; mutable_ = false } in
        (v.name, [ v ])
  in
  let inner =
    {
      sc with
      vars = bound @ sc.vars;
      frozen = frozen @ sc.frozen;
      loop = true;
      weight = sc.weight * 4;
    }
  in
  block_lines
    ("for " ^ pattern ^ " in " ^ head source ^ " {")
    (block b inner ~depth:d) "}"

(* A [for] over a range of at most six integers. The upper bound's type
   decides the counter's, and a literal bound makes it an [i64]. *)
and for_range b sc ~depth =
  let r = b.p.r in
  let d = depth - 1 in
  let limit = Pick.between r 0 5 in
  let range, ty =
    if Pick.chance r 0.5 then (Printf.sprintf "0..%d" limit, Int I64)
    else
      let k = Pick.one r int_kinds in
      let n = expr b sc ~depth:d ~known:true (Int k) in
      (Printf.sprintf "0..=(%s & %d)" (operand n) limit, Int k)
  in
  let i = fresh b.p "n" in
  let inner =
    {
      (declare sc i ty ~mutable_:false) with
      loop = true;
      weight = sc.weight * 6;
    }
  in
  block_lines ("for " ^ i ^ " in " ^ range ^ " {") (block b inner ~depth:d) "}"

(* A [while] or a [loop], counted so that it ends. The counter goes up at the
   start of each pass, so a [continue] can't skip it. *)
and counted_loop b sc ~depth =
  let r = b.p.r in
  let d = depth - 1 in
  let w = fresh b.p "w" in
  let limit = Pick.between r 1 4 in
  let inner =
    {
      (declare sc w (Int I64) ~mutable_:true) with
      frozen = w :: sc.frozen;
      loop = true;
      weight = sc.weight * limit;
    }
  in
  let body = block b inner ~depth:d in
  (0, "var " ^ w ^ " = 0")
  ::
  (if Pick.chance r 0.5 then
     block_lines
       (Printf.sprintf "while %s < %d {" w limit)
       ((0, w ^ " += 1") :: body)
       "}"
   else
     block_lines "loop {"
       ((0, w ^ " += 1")
       :: (0, Printf.sprintf "if %s > %d { break }" w limit)
       :: body)
       "}")

and match_stmt b sc ~depth =
  let d = depth - 1 in
  let s, arms = scrutinee b sc ~depth:d in
  let arm (pattern, bound) =
    block_lines (pattern ^ " => {")
      (block b { sc with vars = bound @ sc.vars } ~depth:d)
      "}"
  in
  block_lines ("match " ^ head s.text ^ " {") (List.concat_map arm arms) "}"
