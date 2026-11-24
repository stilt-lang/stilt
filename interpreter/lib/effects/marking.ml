open Tast
module T = Types

let raises (row : T.row) = Option.is_some (T.row_contents row).raise

let callee_row (e : expr) =
  match e.desc with
  | Call (_, _, _, row) -> Some row
  | Call_value (f, _) -> (
      match T.resolve f.ty with Fn (_, _, row) -> Some row | _ -> None)
  | _ -> None

let raising_call e = Option.fold ~none:false ~some:raises (callee_row e)

(* A call that raises only the error type needs no [try] (effects.error-type-raises). *)
let needs_try e =
  match Option.map T.row_contents (callee_row e) with
  | Some { raise = Some t; _ } -> (
      match T.resolve t with Error -> false | _ -> true)
  | Some { raise = None; _ } | None -> false

(* effects.marking: every raising call sits inside the operand of a [try], which may
   be outside the closure literal that holds the call. A [catch]'s arms are
   outside its operand. *)
let unmarked ~file block =
  let found = ref [] in
  let rec visit ~marked (e : expr) =
    if needs_try e && not marked then
      found :=
        Diagnostic.at ~file Code.e0505 e.loc
          "this call can raise, so it is marked: `try …`"
        :: !found;
    match e.desc with
    | Try (operand, catch) ->
        visit ~marked:true operand;
        List.iter
          (fun (a : arm) ->
            List.iter (visit ~marked) (Option.to_list a.guard @ [ a.body ]))
          (Walk.catch_arms catch)
    | _ -> List.iter (visit ~marked) (Walk.children e)
  in
  List.iter (visit ~marked:false) (Walk.block_exprs block);
  List.rev !found

(* The row variable through which a call may raise an error type that the
   arms of a [catch] around it don't expect: one that its callee's row holds,
   written or implicit, unless the row holds a [raise<E>] and the enclosing
   signature pairs the variable with [E] (effects.catch-around-row-variables). A pairing with the
   error type causes no error (errors.error-type). *)
let same_label a b =
  match (a, b) with
  | Raise_label x, Raise_label y -> T.zonk x = T.zonk y
  | Effect_label (e, xs), Effect_label (f, ys) ->
      e = f && List.map T.zonk xs = List.map T.zonk ys
  | Raise_label _, Effect_label _ | Effect_label _, Raise_label _ -> false

let paired ~pairs (v : Hir.var) label =
  (match label with
    | Raise_label e -> T.zonk e = T.Error
    | Effect_label _ -> false)
  || List.exists
       (fun ((w : Hir.var), l) -> w.id = v.id && same_label l label)
       pairs

let show_label = function
  | Raise_label e -> Types_show.to_string (T.zonk e)
  | Effect_label (e, args) ->
      Types_show.effect_to_string (e, List.map T.zonk args)

let raises_through ~pairs (e : expr) =
  match callee_row e with
  | Some row ->
      let raise = (T.row_contents row).raise in
      List.find_opt
        (fun (p : T.row_param) ->
          match raise with
          | None -> true
          | Some e -> not (paired ~pairs p.var (Raise_label e)))
        (T.params row)
  | None -> None

(* effects.catch-around-row-variables, row variables: a [catch] handles every raise that reaches it while
   its operand runs, so no call in the operand may raise through a row
   variable. A call reaches the [catch] unless it is inside a closure literal,
   which runs only through a call of its own, or inside the operand of a
   nearer [catch]. *)
let caught_row_variables ~file ~pairs block =
  let found = ref [] in
  let rec operand (e : expr) =
    Option.iter
      (fun (p : T.row_param) ->
        found :=
          Diagnostic.at ~file Code.e0506 e.loc
            (if p.implicit then
               Printf.sprintf
                 "`%s`'s failures belong to the caller, but the `catch` around \
                  this call would catch them"
                 p.var.name
             else
               Printf.sprintf
                 "the `catch` around this call would also catch what it raises \
                  through `%s`"
                 p.var.name)
          :: !found)
      (raises_through ~pairs e);
    match e.desc with
    | Closure _ -> ()
    | Try (_, Some c) ->
        List.iter
          (fun (a : arm) ->
            List.iter operand (Option.to_list a.guard @ [ a.body ]))
          c.arms
    | _ -> List.iter operand (Walk.children e)
  in
  Walk.iter_block
    (fun (e : expr) ->
      match e.desc with Try (x, Some _) -> operand x | _ -> ())
    block;
  List.rev !found

(* effects.passing-to-paired-variables: a use that gives a variable its callee pairs with [E] a
   row ending in a row variable of the enclosing function needs the enclosing
   signature to pair that variable with [E] too. Each use is reported once,
   and not at all when it is a call that effects.catch-around-row-variables already reports, since the
   same pairing fixes both. *)
let passed_on ~file ~pairs ~caught passed =
  let unpaired (loc, row, e) =
    if List.mem (loc.Ast.line, loc.col) caught then None
    else
      List.find_opt
        (fun (p : T.row_param) -> not (paired ~pairs p.var e))
        (T.params row)
      |> Option.map (fun p ->
          ( loc,
            p,
            show_label e,
            match e with Raise_label _ -> true | _ -> false ))
  in
  List.filter_map unpaired (List.rev passed)
  |> List.sort_uniq compare
  |> List.map (fun (loc, (p : T.row_param), e, raise) ->
      Diagnostic.at ~file Code.e0507 loc
        (if not raise then
           Printf.sprintf
             "`%s` goes where `%s` is handled, so pair them in your signature: \
              write `{%s, %s}` in one of its rows"
             p.var.name e e p.var.name
         else if p.implicit then
           Printf.sprintf
             "`%s`'s failures go where only `%s` may be raised, so its row \
              names it: `raise<%s>`"
             p.var.name e e
         else
           Printf.sprintf
             "`%s` goes where only `%s` may be raised, so pair them in your \
              signature: write `{raise<%s>, %s}` in one of its rows"
             p.var.name e e p.var.name))

(* handlers.with-pairing: a [with] handles every performance of its effect that
   reaches it while its block runs, so no call in the block may perform
   through a row variable of the enclosing function, unless the callee's row
   holds the effect and the signature pairs the variable with it. A call
   reaches the [with] unless it is inside a closure literal or inside the
   block of a nearer [with] of the same effect. *)
let handled_row_variables ~file ~pairs block =
  let found = ref [] in
  let rec inside eff args (e : expr) =
    (match callee_row e with
    | Some row ->
        let holds = Option.is_some (T.find_effect eff row) in
        Option.iter
          (fun (p : T.row_param) ->
            found :=
              Diagnostic.at ~file Code.e0516 e.loc
                (Printf.sprintf
                   "the `with` around this call would also handle what it \
                    performs through `%s`, which belongs to the caller; pair \
                    them in your signature: write `{%s, %s}` in one of its \
                    rows"
                   p.var.name eff.name p.var.name)
              :: !found)
          (List.find_opt
             (fun (p : T.row_param) ->
               not (holds && paired ~pairs p.var (Effect_label (eff, args))))
             (T.params row))
    | None -> ());
    match e.desc with
    | Closure _ -> ()
    | With (h, inner, _, b) when inner = eff ->
        inside eff args h;
        ignore b
    | _ -> List.iter (inside eff args) (Walk.children e)
  in
  Walk.iter_block
    (fun (e : expr) ->
      match e.desc with
      | With (_, eff, args, b) ->
          List.iter (inside eff args) (Walk.block_exprs b)
      | _ -> ())
    block;
  List.sort_uniq compare !found

let errors ~file ~pairs ~passed block =
  let caught = caught_row_variables ~file ~pairs block in
  unmarked ~file block @ caught
  @ handled_row_variables ~file ~pairs block
  @ passed_on ~file ~pairs
      ~caught:(List.map (fun (d : Diagnostic.t) -> (d.line, d.col)) caught)
      passed

(* effects.catch-alls-need-reason: a catch-all is an arm with no guard whose pattern is [_] or a
   variable. *)
let catch_all (a : arm) =
  Option.is_none a.guard
  && match a.pattern.pat with P_wild | P_bind _ -> true | _ -> false

let reraises (a : arm) =
  match a.body.desc with
  | Raise _ -> true
  | Block stmts -> (
      match List.rev stmts with
      | { stmt = Expr { desc = Raise _; _ }; _ } :: _ -> true
      | _ -> false)
  | _ -> false

(* effects.catch-alls-need-reason: a catch-all whose variable its body refers to shows, wraps or
   passes on the error. A later binding with the same name is another
   variable, with another id. *)
let uses_error (a : arm) =
  match a.pattern.pat with
  | P_bind v ->
      Walk.exists
        (fun (e : expr) ->
          match e.desc with Local u -> u.id = v.id | _ -> false)
        a.body
  | _ -> false

(* effects.catch: a [catch] whose operand raises nothing handles [Never]. *)
let handles_never (c : catch) = T.resolve c.error = T.never

(* effects.empty-try, empty [try]s, and effects.catch-alls-need-reason, catch-alls with neither a raise, a use
   of their error nor a reason. *)
let warnings ~file block =
  let found = ref [] in
  let warn code loc message =
    found := Diagnostic.at ~file code loc message :: !found
  in
  Walk.iter_block
    (fun (e : expr) ->
      match e.desc with
      | Try (operand, None) ->
          (* An operand that holds an expression of the error type may raise
             it (errors.error-type-raises). *)
          let raises (e : expr) = raising_call e || T.resolve e.ty = T.Error in
          if not (Walk.exists raises operand) then
            warn Code.w0500 e.loc "nothing in this `try` can raise"
      | Try (_, Some c) when handles_never c ->
          (* No arm can run, which this warning already says. *)
          warn Code.w0500 e.loc "nothing in this `try` can raise"
      (* A [catch] handles the error type with no diagnostic (effects.error-type-raises). *)
      | Try (_, Some c) when T.resolve c.error = T.Error -> ()
      | Try (_, Some c) ->
          List.iter
            (fun (a : arm) ->
              if
                catch_all a && (not a.because)
                && (not (reraises a))
                && not (uses_error a)
              then
                warn Code.w0501 a.pattern.ploc
                  "this arm catches every error and drops it, so it raises \
                   again, uses the error or gives a reason: `because \"…\"`")
            c.arms
      | _ -> ())
    block;
  List.rev !found
