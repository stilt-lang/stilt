(* The evaluation of expressions, statements, patterns and calls, a tree walk
   over the elaborated program. Values are immutable, so a copy is the value
   itself (values.value-semantics). OCaml evaluates the arguments of a function from right to
   left, so every evaluation that must happen in order is bound with [let]
   first. *)

open Tast
open Value
open Eval_state
open Eval_types
open Eval_operators
open Eval_targets
open Eval_traits
open Eval_places
open Eval_natives

let rec is_place (e : expr) =
  match e.desc with
  | Local _ | Project _ -> true
  | Field (base, _) | Tuple_field (base, _) | Index (base, _) -> is_place base
  | _ -> false

(* A place with its index expressions evaluated (values.left-to-right and values.index-reads): a place of
   the current frame, or a projection's call with its arguments evaluated,
   and the steps written after it, which yields a place of its own frame
   when it is opened (projections.call-is-place and projections.when-projection-runs). *)
type prepared =
  | Direct of place
  | Deferred of {
      target : target;
      args : (value, prepared) Either.t list;
      loc : Ast.loc;
      steps : step list;
    }

let rec expr t fr (e : expr) : value =
  match e.desc with
  | Int text -> int_literal (concrete fr e.ty) text
  | Float text -> float_literal (concrete fr e.ty) text
  | Str s -> Str s
  | Bool b -> Bool b
  | Interpolated segments -> interpolated t fr segments
  | Local v -> Hashtbl.find fr.locals (local_id v.id)
  | Value_param v -> value_param fr v (concrete fr e.ty)
  | Constant item -> Lazy.force (Hashtbl.find t.constants item)
  | Member_constant (owner, name, _) ->
      Lazy.force (Hashtbl.find t.member_constants (owner, name))
  | Trait_constant (trait, name, ty) ->
      trait_constant t trait name (concrete fr ty)
  | Callee (c, targs) ->
      Fn (Function (concrete_callee fr c, List.map (concrete fr) targs))
  | Constructor (item, _) -> Fn (Constructor item)
  | Generalize (vars, x) -> generalize vars (expr t fr x)
  | Instantiate (x, ts) -> instantiate (List.map (concrete fr) ts) (expr t fr x)
  | Construct (item, _, es) -> Variant (item, List.map (expr t fr) es)
  | Record (item, _, fields) -> Eval_records.record ~expr t fr item fields
  | Update (base, fields) -> Eval_records.update ~expr t fr base fields
  | Tuple es -> Tuple (Eval_records.elements ~expr t fr es)
  | List es -> List (Vec.of_list (Eval_records.elements ~expr t fr es))
  | Spread _ -> invalid_arg "Eval_exprs.expr: a spread outside its tuple"
  | Field (x, f) -> Eval_records.field (expr t fr x) f
  | Tuple_field (x, i) -> Eval_records.tuple_field (expr t fr x) i
  | Call (Operation (eff, name), _, args, _) -> perform t fr e.loc eff name args
  | Call (c, targs, args, _) ->
      let target =
        target t (concrete_callee fr c) (List.map (concrete fr) targs)
      in
      call t fr e.loc target args
  | Call_value (f, args) -> (
      match expr t fr f with
      | Fn fn -> call t fr e.loc (target_of_fn t fn) args
      | _ -> invalid_arg "Eval_exprs.expr: call of a value")
  | Project _ -> project_read t fr e
  | Index (container, key) ->
      let c = expr t fr container in
      let k = expr t fr key in
      index t fr e.loc (concrete fr container.ty) c k
  | Unary (Neg, { desc = Int text; _ }) ->
      negative_literal (concrete fr e.ty) text
  | Unary (op, x) ->
      let v = expr t fr x in
      unary fr e.loc op (concrete fr e.ty) v
  | Binary (op, a, b) -> binary_expr t fr e.loc op a b
  | Else _ | Try _ | Raise _ | Return _ | Break | Continue | Closure _ | Block _
  | If _ | If_let _ | Match _ | Loop _ | While _ | For _ ->
      control t fr e
  | Hole -> panic fr e.loc "hole" "reached a hole"
  | Handler _ | With _ | Resume _ | When _ -> handling t fr e
  (* meta.erasure: a staging annotation runs as the erased form. *)
  | Comptime x -> expr t fr x
  | Reflect r -> Eval_meta.reflect t fr r
  (* macros.splices and macros.outside-run *)
  | Quote q -> Eval_quotes.quote t fr e.loc q
  | Error -> invalid_arg "Eval_exprs.expr: an expression with an error"

and binary_expr t fr loc op a b =
  match op with
  | And -> if truth (expr t fr a) then expr t fr b else Bool false
  | Or -> if truth (expr t fr a) then Bool true else expr t fr b
  | _ ->
      let x = expr t fr a in
      let y = expr t fr b in
      binary t fr loc op ~static:a.ty ~right:(concrete fr b.ty)
        (concrete fr a.ty) x y

(* handlers.handler-literals, handlers.with and handlers.resuming: handler literals, [with] and [resume]. *)
and handling t fr (e : expr) =
  match e.desc with
  | Handler h -> Eval_handlers.literal t fr ~expr h
  | With (h, _, _, b) ->
      Eval_handlers.install t fr e.loc (expr t fr h) (fun () -> block t fr b)
  | Resume x ->
      Eval_handlers.resume (Option.fold ~none:unit ~some:(expr t fr) x)
  | When (names, b) ->
      Eval_when.run t fr e.loc ~expr names (fun () -> block t fr b)
  | _ -> invalid_arg "Eval_exprs.handling"

and interpolated t fr segments = Eval_interp.interpolated ~expr t fr segments

(* The expressions that decide what runs next: branches, jumps, raises,
   closures and loops. *)
and control t fr (e : expr) =
  match e.desc with
  | Else (a, b) -> (
      match expr t fr a with
      | Variant ({ name = "Some"; _ }, [ x ]) -> x
      | _ -> expr t fr b)
  | Try (x, None) -> expr t fr x
  | Try (x, Some c) -> (
      match expr t fr x with
      | v -> v
      | exception Raised error -> arms t fr c.arms error)
  | Raise x -> raise (Raised (expr t fr x))
  | Return x ->
      raise (Return (match x with Some x -> expr t fr x | None -> unit))
  | Break -> raise Break
  | Continue -> raise Continue
  | Closure (params, _, body) ->
      (* Captures copies of the variables in scope (expressions.capture). *)
      let captured = Eval_when.captured fr in
      Fn (Closure { params; body; captured; tenv = fr.tenv; home = fr.home })
  | Block b -> block t fr b
  | If (c, b, alt) -> (
      if truth (expr t fr c) then block t fr b
      else match alt with Some x -> expr t fr x | None -> unit)
  | If_let (p, x, b, alt) -> (
      if
        (* Matched as an arm without a guard (expressions.if-let-matching). *)
        pattern t fr p (expr t fr x)
      then block t fr b
      else match alt with Some x -> expr t fr x | None -> unit)
  | Match (x, a) ->
      let v = expr t fr x in
      arms t fr a v
  | Loop b ->
      repeat t fr b (fun () -> true);
      unit
  | While (c, b) ->
      repeat t fr b (fun () -> truth (expr t fr c));
      unit
  | For (p, iterable, b) ->
      let each v =
        ignore (pattern t fr p v);
        Eval_loops.turn ~block t fr b
      in
      (match iterable with
      (* meta.fields and meta.variant-cases *)
      | Iter s when Eval_meta.iterated (concrete fr s.ty) ->
          ignore (expr t fr s);
          Eval_meta.iterate t fr (concrete fr s.ty) p each
      | _ -> iterate t fr iterable each);
      unit
  | _ -> invalid_arg "Eval_exprs.control"

(* Loops (expressions.loops), whose bodies are blocks. *)
and repeat t fr b more = Eval_loops.repeat ~block t fr b more
and iterate t fr iterable each = Eval_loops.iterate ~expr t fr iterable each

and block t fr = function
  | [] -> unit
  | [ { stmt = Expr e; _ } ] -> expr t fr e
  | s :: rest ->
      stmt t fr s;
      block t fr rest

and stmt t fr (s : stmt) =
  match s.stmt with
  | Let b | Var b -> (
      let v = expr t fr b.value in
      if not (pattern t fr b.pattern v) then
        match b.otherwise with
        | Some x -> ignore (expr t fr x)
        | None -> invalid_arg "Eval_exprs.stmt: refutable binding")
  | Assign (None, p, x) ->
      (* values.assignment-order: the place's index expressions, then the value, then
         the store, where a projection's call starts (projections.when-projection-runs). *)
      let prepared = prepare t fr p in
      let v = expr t fr x in
      open_place t fr prepared (fun (pfr, pl) -> store t pfr pl v)
  | Assign (Some op, p, x) ->
      (* values.compound-assignment-order *)
      let prepared = prepare t fr p in
      let v = expr t fr x in
      let ty = concrete fr p.ty in
      let right = concrete fr x.ty in
      open_place t fr prepared (fun (pfr, pl) ->
          let current = read t pfr pl in
          store t pfr pl (binary t fr s.at op ~static:p.ty ~right ty current v))
  | Assert e ->
      if not (truth (expr t fr e)) then
        panic fr s.at "assert" "the assertion is false"
  | Yield p when is_place p ->
      (* projections.yield: the place is handed to the caller, and the body
         goes on once the caller is done with it. *)
      with_place t fr p (fun (pfr, pl) ->
          Effect.perform (Eval_places.Yield (pfr, pl)))
  | Yield x ->
      (* A view that no place holds, bound to a temporary of the statement. *)
      let v = expr t fr x in
      let tmp = temporary () in
      Hashtbl.replace fr.locals tmp v;
      Effect.perform (Eval_places.Yield (fr, (tmp, [])))
  | Expr e -> ignore (expr t fr e)

(* Patterns (patterns.pattern-forms), whose guards and constants are expressions. *)
and arms t fr arms v = Eval_patterns.arms ~expr t fr arms v
and pattern t fr p v = Eval_patterns.pattern ~expr t fr p v

(* Places (expressions.places; values.assignment-order and values.compound-assignment-order; projections.call-is-place and projections.when-projection-runs). A place
   is prepared, which evaluates its index expressions and a projection's
   arguments in their turn, and then opened, which runs each projection it
   is rooted in to its [yield] for the access and resumes it after. *)

and prepare t fr (e : expr) : prepared =
  let extend prepared step =
    match prepared with
    | Direct (root, steps) -> Direct (root, steps @ [ step ])
    | Deferred d -> Deferred { d with steps = d.steps @ [ step ] }
  in
  match e.desc with
  | Local v -> Direct (local_id v.id, [])
  | Field (base, f) -> extend (prepare t fr base) (At_field f)
  | Tuple_field (base, i) -> extend (prepare t fr base) (At_elem i)
  | Index (base, key) ->
      let prepared = prepare t fr base in
      let k = expr t fr key in
      extend prepared (At_key (k, concrete fr base.ty, e.loc))
  | Project (c, targs, args, _) ->
      let target =
        target t (concrete_callee fr c) (List.map (concrete fr) targs)
      in
      Deferred
        { target; args = prepare_args t fr args; loc = e.loc; steps = [] }
  | _ -> invalid_arg "Eval_exprs.prepare"

(* The arguments of a call, evaluated from left to right: the value of each
   [let] argument, a spread's values (variadics.spread-expressions), and the prepared place
   of each [inout] one. *)
and prepare_args t fr args =
  List.concat_map
    (fun (a : arg) ->
      match a.mode with
      | Inout -> [ Either.Right (prepare t fr a.value) ]
      | Let ->
          List.map Either.left (Eval_records.elements ~expr t fr [ a.value ]))
    args

(* Opens a prepared place for the access [k]: the place of a frame, which a
   projection's call yields from its own frame, held until [k] is done. *)
and open_place : 'a. t -> frame -> prepared -> (frame * place -> 'a) -> 'a =
 fun t fr prepared k ->
  match prepared with
  | Direct pl -> k (fr, pl)
  | Deferred d ->
      project t fr d.loc d.target d.args (fun (pfr, (root, steps)) ->
          k (pfr, (root, steps @ d.steps)))

(* Opens the prepared [inout] arguments of a call, from left to right, each
   held for the rest (projections.when-projection-runs). *)
and open_args :
    'a.
    t ->
    frame ->
    (value, prepared) Either.t list ->
    ((value, frame * place) Either.t list -> 'a) ->
    'a =
 fun t fr prepared k ->
  let rec go acc = function
    | [] -> k (List.rev acc)
    | Either.Left v :: rest -> go (Either.Left v :: acc) rest
    | Either.Right p :: rest ->
        open_place t fr p (fun access -> go (Either.Right access :: acc) rest)
  in
  go [] prepared

and with_place : 'a. t -> frame -> expr -> (frame * place -> 'a) -> 'a =
 fun t fr e k -> open_place t fr (prepare t fr e) k

(* Calls (values.inout-arguments and values.left-to-right) *)

(* Evaluates the arguments from left to right, and calls the target. An
   [inout] argument is a place, whose index expressions are evaluated in its
   turn. The place is read when the call starts, after every argument, so
   that changes made by later arguments reach the callee, and it gets the
   callee's changes when the callee returns or raises. *)
and call t fr loc target args =
  match (target, args) with
  (* The natives of [std.view] that take the place of a list or a view
     [inout], and give a window into it (projections.writable-views). *)
  | Native_code (Function { home = "std.view"; name }, _), _
    when List.mem name [ "into"; "part"; "split" ] ->
      let call f a b =
        match f with
        | Fn fn -> apply t fr loc (target_of_fn t fn) [| a; b |]
        | _ -> invalid_arg "Eval_exprs.windows: split"
      in
      Eval_windows.native t fr loc ~opened:(open_place t fr) ~call name
        (prepare_args t fr args)
  | _ ->
      open_args t fr (prepare_args t fr args) (fun accesses ->
          run_call t fr loc target accesses)

(* handlers.performing-operation: a performance, whose arguments are evaluated where it is,
   before its handler runs. *)
and perform t fr loc eff name args =
  let prepared = prepare_args t fr args in
  let call fn =
    open_args t fr prepared (fun accesses ->
        run_call t fr loc (target_of_fn t fn) accesses)
  in
  let values () =
    Array.of_list
      (List.map
         (Either.fold ~left:Fun.id ~right:(fun p ->
              open_place t fr p (fun (pfr, pl) -> read t pfr pl)))
         prepared)
  in
  Eval_handlers.perform ~call ~values eff name

(* Runs a call on its evaluated arguments: the [inout] ones are read when
   the call starts and written back when it returns, raises, or a handler
   ends it (values.inout-arguments; handlers.call-that-handler-ends). *)
and run_call t fr loc target accesses =
  let values =
    Array.of_list
      (List.map
         (Either.fold ~left:Fun.id ~right:(fun (pfr, pl) -> read t pfr pl))
         accesses)
  in
  let write_back () =
    List.iteri
      (fun i ->
        Either.iter ~left:ignore ~right:(fun (pfr, pl) ->
            store t pfr pl values.(i)))
      accesses
  in
  let places =
    List.filter_map
      (function Either.Left _ -> None | Right access -> Some access)
      accesses
  in
  match apply ~places t fr loc target values with
  | v ->
      write_back ();
      v
  | exception ((Raised _ | Access_raised _ | Abandoned) as ended) ->
      write_back ();
      raise ended

(* projections.call-is-place: a read of a projection's call copies the yielded place's
   value out, and the projection resumes; a window in the copy that writes
   an [inout] parameter of the projection writes the caller's argument
   instead (projections.what-view-writes and projections.reaching-written-source). *)
and project_read t fr (e : expr) =
  match prepare t fr e with
  | Direct pl -> read t fr pl
  | Deferred d ->
      let fix accesses = Eval_windows.copied ~target:d.target ~accesses in
      project ~fix t fr d.loc d.target d.args (fun (pfr, (root, steps)) ->
          read t pfr (root, steps @ d.steps))

(* The call of a projection on its prepared arguments, for the access [k]:
   the body runs to its [yield], [k] runs on the yielded place, and the body
   resumes, unless [k] raised, which the body's own [catch] arms don't see
   (projections.when-projection-runs and projections.raising-during-access). [fix] is applied to what [k] gives, with the
   caller's places for the arguments and the frame of the yielded place. *)
and project :
    'a.
    ?fix:((value, frame * place) Either.t list -> frame -> 'a -> 'a) ->
    t ->
    frame ->
    Ast.loc ->
    target ->
    (value, prepared) Either.t list ->
    (frame * place -> 'a) ->
    'a =
 fun ?(fix = fun _ _ v -> v) t fr loc target args k ->
  open_args t fr args (fun accesses ->
      let me = temporary () in
      let result = ref None in
      let handler =
        {
          Effect.Deep.retc = ignore;
          exnc =
            (function
            | Access_raised (id, error) when id = me -> raise (Raised error)
            | e -> raise e);
          effc =
            (fun (type a) (eff : a Effect.t) ->
              match eff with
              | Eval_places.Yield (pfr, pl) ->
                  Some
                    (fun (cont : (a, unit) Effect.Deep.continuation) ->
                      match fix accesses pfr (k (pfr, pl)) with
                      | v ->
                          result := Some v;
                          Effect.Deep.continue cont ()
                      | exception Raised error ->
                          Effect.Deep.discontinue cont
                            (Access_raised (me, error))
                      | exception e -> Effect.Deep.discontinue cont e)
              | _ -> None);
        }
      in
      Effect.Deep.match_with (run_call t fr loc target) accesses handler;
      match !result with
      | Some v -> v
      | None -> invalid_arg "Eval_exprs.project: no yield")

(* Calls a target on the values of its arguments. The callee leaves the final
   values of its [inout] parameters in [values]. A window the callee returns
   into an [inout] parameter writes the caller's argument at [places]
   instead (projections.what-view-writes). *)
and apply ?(places = []) t fr loc target values =
  called target;
  match target with
  | Body (f, tenv) ->
      entering ~home:f.home ~at:f.at (fun () ->
          body ~places t fr loc f tenv values)
  | Closure_body c ->
      let callee = enter t fr loc ~home:c.home ~tenv:c.tenv in
      Imap.iter (Hashtbl.replace callee.locals) c.captured;
      List.iteri (fun i p -> ignore (pattern t callee p values.(i))) c.params;
      let finish () =
        List.iteri
          (fun i (p : pattern) ->
            match p.pat with
            | P_bind v -> values.(i) <- Hashtbl.find callee.locals v.id
            | _ -> ())
          c.params
      in
      entering ~home:"" ~at:loc (fun () ->
          returning finish (fun () -> expr t callee c.body))
  | Native_code (callee, targs) ->
      (* A native of [std.view] reads a writable view as the part it views
         (projections.places-through-views). *)
      let values =
        match callee with
        | Function { home = "std.view"; _ }
        | Member ({ home = "std.view"; _ }, _) ->
            Array.map (Eval_windows.thaw t fr) values
        | _ -> values
      in
      guard fr loc (fun () -> native t fr loc callee targs values)
  | Structural (name, ty) ->
      (* A writable view has the structural impls of the part it views
         (projections.places-through-views). *)
      structural t fr loc name ty (Array.map (Eval_windows.thaw t fr) values)
  | Variant_of item -> Variant (item, Array.to_list values)

(* Calls a declared function on the values of its arguments. *)
and body ~places t fr loc (f : fn_def) tenv values =
  let code =
    match f.body with
    | Code b -> b
    | Broken -> check_error t ~home:f.home f.at
    | Native -> invalid_arg "Eval_exprs.apply"
  in
  let callee = enter t fr loc ~home:f.home ~tenv in
  List.iteri
    (fun i (_, (v : Hir.var)) -> Hashtbl.replace callee.locals v.id values.(i))
    f.params;
  let finish () =
    List.iteri
      (fun i (mode, (v : Hir.var)) ->
        if mode = Ast.Inout then values.(i) <- Hashtbl.find callee.locals v.id)
      f.params
  in
  let inouts =
    List.filter_map
      (fun (mode, (v : Hir.var)) ->
        if mode = Ast.Inout then Some v.id else None)
      f.params
  in
  let targets =
    if List.length inouts = List.length places then List.combine inouts places
    else []
  in
  Eval_windows.retarget ~callee targets
    (returning finish (fun () -> block t callee code))
