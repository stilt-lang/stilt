(* Where a view escapes (views.escaping): a view leaves the scope that binds
   one of its sources nowhere, and a function only through its result, from
   its [let] parameters. Each escape is E0422, at the expression that
   escapes. *)

open Tast
module T = Types
module V = Views_types
module S = Views_sources

(* The [return]s of a body, outside the closures in it. *)
let rec returns (e : expr) =
  match e.desc with
  | Closure _ -> []
  | Return (Some x) -> x :: returns x
  | _ -> List.concat_map returns (Walk.children e)

let block_returns b = List.concat_map returns (Walk.block_exprs b)

(* The value of a body that leaves it, as its result: an expression at the
   end of its branches. Each of them gets its own error. *)
let rec leaves check (r : expr) =
  let tail b =
    match List.rev b with
    | { stmt = Expr e; _ } :: _ -> leaves check e
    | _ -> ()
  in
  match r.desc with
  | Block b -> tail b
  | If (_, b, alt) | If_let (_, _, b, alt) ->
      tail b;
      Option.iter (leaves check) alt
  | Match (_, arms) -> List.iter (fun (a : arm) -> leaves check a.body) arms
  | Try (x, c) ->
      leaves check x;
      List.iter (fun (a : arm) -> leaves check a.body) (Walk.catch_arms c)
  | Else (a, b) ->
      leaves check a;
      leaves check b
  | Comptime x -> leaves check x
  | _ -> check r

let outlives source =
  Printf.sprintf
    "this view of %s outlives it: a function's result may view only its `let` \
     parameters"
    (S.describe source)

let captures t (e : expr) =
  Printf.sprintf
    "this closure captures a view of %s, and leaves the function, which the \
     view can't"
    (String.concat ", " (List.map S.describe (S.sources t e)))

(* A value that leaves a body: a view whose sources aren't all [allowed],
   or a closure that captures a view, at its literal. A view that reads an
   [inout] parameter of a function's result is E0428 (projections.results-that-write). *)
let leaving ?(inouts = []) t report ~allowed (r : expr) =
  let reads_inout = function
    | S.Place p -> List.mem p.root.id inouts
    | Written _ | Temporary _ -> false
  in
  if V.is_view r.ty then
    match List.find_opt (fun s -> not (allowed s)) (S.sources t r) with
    | Some s when reads_inout s ->
        report Code.e0428 r.loc
          (Printf.sprintf
             "this view reads %s, which the result must write: make it with \
              `view.into(inout %s, …)`"
             (S.describe s) (S.describe_bare s))
    | Some s -> report Code.e0422 r.loc (outlives s)
    | None -> ()
  else
    Option.iter (fun at -> report Code.e0422 at (captures t r)) (S.closure t r)

(* The arguments that a call gives to [escaping] parameters, which keep them
   (effects.escaping-parameters): a closure that captures a view escapes there. *)
let kept env t report (e : expr) =
  let key : callee -> Implicit_names.key = function
    | Function item -> Function item
    | Member (owner, name) -> Member (owner, name)
    | Trait_method (trait, name, _) -> Built_in (trait, name)
    | Operation _ -> invalid_arg "Views_escapes.kept"
  in
  match e.desc with
  (* An operation's parameters keep nothing past the performance (handlers.performing-operation). *)
  | Call (Operation _, _, _, _) -> ()
  | Call (callee, _, args, _) | Project (callee, _, args, _) -> (
      match Implicit_names.signature env (key callee) with
      | Some s ->
          let passing = Env.passing s in
          List.iteri
            (fun i (a : arg) ->
              match (List.nth_opt s.params i, List.nth_opt passing i) with
              (* shared.tasks-and-modes, and par.what-runs-in-parallel: a demand on the
                 thread axes reports the argument (E0431, E0432). *)
              | _ when Demands.demanded callee i -> ()
              | Some (_, T.Fn _), Some false ->
                  Option.iter
                    (fun at -> report Code.e0422 at (captures t a.value))
                    (S.closure t a.value)
              | _ -> ())
            args
      | None -> ())
  | _ -> ()

(* The variables of a block whose type is viewable or a view type, by the
   uses that name them. *)
let viewing_locals block =
  let found = ref [] in
  Walk.iter_block
    (fun (e : expr) ->
      match e.desc with
      | Local v when V.viewable e.ty || V.is_view e.ty ->
          found := v.id :: !found
      | _ -> ())
    block;
  !found

(* The results of a function's body may view its [let] parameters of a
   viewable or a view type (views.across-calls), not a field of a record
   parameter, which views the callee's copy, and write its [inout] parameters
   (projections.results-that-write). *)
let function_results t report ~params block =
  let viewing = viewing_locals block in
  let lets =
    List.filter_map
      (fun (mode, (v : Hir.var)) ->
        if mode = (Let : Ast.mode) && List.mem v.id viewing then Some v.id
        else None)
      params
  in
  let inouts =
    List.map (fun (v : Hir.var) -> v.id) (Modes_places.inout_params params)
  in
  let allowed = function
    | S.Place p -> List.mem p.root.id lets
    | Written p -> List.mem p.root.id inouts
    | Temporary _ -> false
  in
  let tail =
    match List.rev block with { stmt = Expr e; _ } :: _ -> [ e ] | _ -> []
  in
  List.iter
    (leaves (leaving ~inouts t report ~allowed))
    (tail @ block_returns block)

(* A closure's results may view what it captures and its [let] parameters,
   but nothing it binds itself. *)
let closure_results t report (e : expr) =
  match e.desc with
  | Closure (params, _, body) ->
      let inouts =
        match T.resolve e.ty with
        | Fn (modes, _, _) when List.length modes = List.length params ->
            List.concat
              (List.map2
                 (fun (mode, _) (p : pattern) ->
                   if mode = (Inout : Ast.mode) then Modes_places.pattern_vars p
                   else [])
                 modes params)
        | _ -> []
      in
      let own = S.bound_in body @ inouts in
      let allowed = function
        | S.Place p | Written p -> not (List.mem p.root.id own)
        | Temporary _ -> false
      in
      List.iter (leaves (leaving t report ~allowed)) (body :: returns body)
  | _ -> ()

(* The variables that a block's statements bind, whose scope ends with it. *)
let block_bindings b =
  List.concat_map
    (fun (s : stmt) ->
      match s.stmt with
      | Let bd | Var bd -> Modes_places.pattern_vars bd.pattern
      | Assign _ | Assert _ | Yield _ | Expr _ -> [])
    b

let block_value b =
  match List.rev b with { stmt = Expr e; _ } :: _ -> Some e | _ -> None

(* A value that leaves the scope of the bindings [bound], viewing one of
   them, or a closure that captures such a view, at its literal. *)
let ending t report bound (r : expr) =
  let own = function
    | S.Place p | Written p -> List.mem p.root.id bound
    | Temporary _ -> false
  in
  match List.find_opt own (S.sources t r) with
  | Some s when V.is_view r.ty ->
      report Code.e0422 r.loc
        (Printf.sprintf
           "this view of %s outlives it: %s ends with the scope that binds it"
           (S.describe s) (S.describe s))
  | Some _ ->
      Option.iter
        (fun at -> report Code.e0422 at (captures t r))
        (S.closure t r)
  | None -> ()

(* A view leaves the scope that binds one of its sources nowhere: the value
   of a block may not view a binding the block makes, nor that of an arm or
   an [if let] a binding of its pattern, nor that of a [when] a name it holds,
   whose value it releases when its block ends (shared.when). A loop's body
   has no value. *)
let scope_ends t report (e : expr) =
  let check bound value = leaves (ending t report bound) value in
  let block extra b =
    Option.iter (check (extra @ block_bindings b)) (block_value b)
  in
  let arms =
    List.iter (fun (a : arm) ->
        check (Modes_places.pattern_vars a.pattern) a.body)
  in
  match e.desc with
  | Block b | If (_, b, _) -> block [] b
  | If_let (p, _, b, _) -> block (Modes_places.pattern_vars p) b
  | When (names, b) -> block (List.map (fun (_, (v : Hir.var)) -> v.id) names) b
  | Match (_, a) -> arms a
  | Try (_, c) -> arms (Walk.catch_arms c)
  | _ -> ()

(* A view assigned to an [inout] parameter goes back to the caller. *)
let assigned t report ~params (s : stmt) =
  match s.stmt with
  | Assign (_, place, value) -> (
      match Modes_places.place place with
      | Some p
        when List.exists
               (fun (mode, (v : Hir.var)) ->
                 mode = (Inout : Ast.mode) && v.id = p.root.id)
               params
             && S.carries t value -> (
          match (S.sources t value, S.closure t value) with
          | _, Some at -> report Code.e0422 at (captures t value)
          | source :: _, None -> report Code.e0422 value.loc (outlives source)
          | [], None -> ())
      | _ -> ())
  | Let _ | Var _ | Assert _ | Yield _ | Expr _ -> ()

(* A view assigned to a variable that outlives the scope that binds one of
   the view's sources. [scopes] holds the bindings of each scope around the
   code, the innermost first: a block's, an arm's or an [if let]'s pattern's,
   a [for]'s pattern's, the names a [when] holds, and a closure's
   parameters. *)
let rec scoped t report scopes (e : expr) =
  let visit = scoped t report scopes in
  let inner extra b = scoped_block t report scopes ~extra b in
  let arm (a : arm) =
    let scopes = Modes_places.pattern_vars a.pattern :: scopes in
    Option.iter (scoped t report scopes) a.guard;
    scoped t report scopes a.body
  in
  match e.desc with
  | If_let (p, x, b, alt) ->
      visit x;
      inner (Modes_places.pattern_vars p) b;
      Option.iter visit alt
  | Match (x, arms) ->
      visit x;
      List.iter arm arms
  | Try (x, c) ->
      visit x;
      List.iter arm (Walk.catch_arms c)
  | For (p, it, b) ->
      (match it with
      | Iter x -> visit x
      | Range (a, z, _) ->
          visit a;
          visit z);
      inner (Modes_places.pattern_vars p) b
  | When (names, b) ->
      List.iter (fun (handle, _) -> visit handle) names;
      inner (List.map (fun (_, (v : Hir.var)) -> v.id) names) b
  | Closure (ps, _, body) ->
      scoped t report
        (List.concat_map Modes_places.pattern_vars ps :: scopes)
        body
  | _ ->
      List.iter
        (function Walk.Expr e -> visit e | Block b -> inner [] b)
        (Walk.parts e)

and scoped_block t report scopes ~extra b =
  let scopes = (extra @ block_bindings b) :: scopes in
  List.iter
    (fun (s : stmt) ->
      (match s.stmt with
      | Assign (None, { desc = Local w; _ }, value) ->
          (* The bindings of the scopes inside the one that binds [w], which
             are all of them for a parameter. *)
          let rec inside = function
            | [] -> []
            | scope :: rest ->
                if List.mem w.id scope then [] else scope @ inside rest
          in
          ending t report (inside scopes) value
      | Assign _ | Let _ | Var _ | Assert _ | Yield _ | Expr _ -> ());
      List.iter (scoped t report scopes) (Walk.stmt_exprs s))
    b

(* The escapes at an expression of a body: a closure that captures a view
   given to an [escaping] parameter, a scope's value, and a closure's
   results. *)
let expr env t report e =
  kept env t report e;
  scope_ends t report e;
  closure_results t report e

let stmt = assigned

(* The escapes of a body as a whole: its results, and its assignments. *)
let body t report ~params block =
  function_results t report ~params block;
  scoped_block t report [] ~extra:[] block
