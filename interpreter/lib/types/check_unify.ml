(* Unification of types, and of effect rows (effects.inference and effects.function-values). *)

module T = Types

type problem =
  | Missing_io
  | Missing_raise of T.ty
  | Raise_mismatch of T.ty * T.ty
  | Missing_var of Hir.var
  | Cyclic_raise of T.ty (* A raise whose type would hold the row itself. *)
  | Missing_effect of Hir.item
  | Effect_mismatch of Hir.item * T.ty list * T.ty list
(* handlers.effects-in-rows: an effect performed with other type arguments than
         the row's. *)

let rec open_var (r : T.row) =
  match r.tail with
  | Row_var rv -> (
      match T.row_state rv with Open _ -> Some rv | Link r -> open_var r)
  | Closed | Row_params _ -> None

let numeric (item : Hir.item) =
  item.home = "std.prelude"
  && (List.mem item.name T.integer_types || List.mem item.name T.float_types)

let float (item : Hir.item) =
  item.home = "std.prelude" && List.mem item.name T.float_types

(* Meeting the error type taints every variable on the other side, so that
   none is reported as unknown (errors.error-type). *)
let rec unify a b =
  match (T.resolve a, T.resolve b) with
  | Error, t | t, Error ->
      T.taint t;
      true
  | (Var _ as x), (Var _ as y) -> unify_vars x y
  | (Var _ as x), t | t, (Var _ as x) -> (
      match T.unsolved x with
      | None -> false
      | Some v ->
          let fits =
            match (v.kind, t) with
            | Any, _ -> not (T.occurs x t || T.would_escape x t)
            | Int_literal, Con (item, []) -> numeric item
            | Float_literal, Con (item, []) -> float item
            | (Int_literal | Float_literal), _ -> false
          in
          fits
          &&
          (T.solve x t;
           true))
  | Con (i, xs), Con (j, ys) -> i = j && unify_all xs ys
  | App (f, xs), App (g, ys) -> unify f g && unify_all xs ys
  | App (h, xs), t | t, App (h, xs) -> unify_head h xs t
  | Param p, Param q -> p.id = q.id
  (* generics.equal-types: value arguments are equal by value. *)
  | Value x, Value y -> x = y
  | Tuple xs, Tuple ys -> unify_elems xs ys
  (* records.anonymous-types: the same fields with the same types. *)
  | Record xs, Record ys ->
      List.map fst xs = List.map fst ys
      && unify_all (List.map snd xs) (List.map snd ys)
  | Spread (p, x), Spread (q, y) -> unify p q && unify x y
  | Fn (ps, r, row), Fn (qs, s, row') ->
      unify_params ps qs && unify r s && unify_row row row'
  (* handlers.handler-types *)
  | Handler h, Handler k ->
      h.eff = k.eff && unify_all h.hargs k.hargs
      && (match (h.answer, k.answer) with
        | None, None -> true
        | Some x, Some y -> unify x y
        | _ -> false)
      && unify_row h.hrow k.hrow
  (* polymorphism.instantiation: the same up to the names of their type parameters. *)
  | Forall p, Forall q -> (
      match Env_signatures.renaming p q with
      | Some rename -> unify p.body (rename q.body)
      | None -> false)
  | _ -> false

(* Two variables: the one of the narrower kind stays. *)
and unify_vars x y =
  match (T.unsolved x, T.unsolved y) with
  | Some vx, Some vy when vx.id = vy.id -> true
  | Some vx, Some vy -> (
      match (vx.kind, vy.kind) with
      | Any, _ ->
          T.solve x y;
          true
      | _, Any ->
          T.solve y x;
          true
      | Int_literal, _ ->
          T.solve x y;
          true
      | _, Int_literal ->
          T.solve y x;
          true
      | Float_literal, Float_literal ->
          T.solve x y;
          true)
  | _ -> false

and unify_all xs ys =
  List.length xs = List.length ys && List.for_all2 unify xs ys

(* variadics.pack-inference: elements of tuples, or parameters of function types, one
   list of which may hold a spread of a pack not yet known: the pack is the
   elements that the other list holds in its place, each a new variable, or
   a spread of the other's pack for a spread there. *)
and unify_elems xs ys =
  match (open_spread xs, open_spread ys) with
  | Some (i, pack), _ -> fill i pack xs ys
  | None, Some (j, pack) -> fill j pack ys xs
  | None, None -> unify_all xs ys

and open_spread ts =
  let rec find i = function
    | [] -> None
    | T.Spread (pack, _) :: _ when Option.is_some (T.unsolved pack) ->
        Some (i, pack)
    | _ :: rest -> find (i + 1) rest
  in
  find 0 ts

and fill i pack xs ys =
  let after = List.length xs - i - 1 in
  let n = List.length ys - i - after in
  n >= 0
  && (not (T.occurs pack (T.Tuple ys)))
  &&
  let origin = Option.get (T.origin pack) in
  let element t =
    match T.resolve t with
    | Spread (q, _) -> T.Spread (q, T.fresh origin)
    | _ -> T.fresh origin
  in
  T.solve pack
    (T.Tuple
       (List.map element (List.filteri (fun j _ -> j >= i && j < i + n) ys)));
  unify_all (T.expand xs) ys

and unify_params ps qs =
  if List.exists (fun (_, t) -> Packs.is_spread t) (ps @ qs) then
    unify_elems (List.map snd ps) (List.map snd qs)
    &&
    match
      ( T.resolve (T.Fn (ps, T.unit, T.empty_row)),
        T.resolve (T.Fn (qs, T.unit, T.empty_row)) )
    with
    | Fn (ps, _, _), Fn (qs, _, _) ->
        List.length ps = List.length qs
        && List.for_all2 (fun (m, _) (n, _) -> m = n) ps qs
    | _ -> false
  else
    List.length ps = List.length qs
    && List.for_all2 (fun (m, x) (n, y) -> m = n && unify x y) ps qs

(* traits.constructor-parameters: a constructor that a variable [h] stands for, applied to
   [xs], is inferred from the head of the type [t] it meets. A tuple or a
   function type, which no constructor heads, solves [h] all the same, which
   makes the application the error type and leaves the bound on [h] unmet
   (E0318). A constructor of another arity is no solution: the types
   differ. *)
and unify_head h xs t =
  match (T.unsolved h, t) with
  | Some _, Con (item, ys) when List.length xs = List.length ys ->
      T.solve h (T.Con (item, []));
      unify_all xs ys
  | Some _, (Tuple _ | Fn _) ->
      T.solve h t;
      true
  | _ -> false

(* Makes two rows one, as two equal function types need. A least row gains
   no effect this way, so it must already hold every effect of the other row
   (effects.function-values). *)
and unify_row a b =
  match (open_var a, open_var b) with
  | Some ra, Some rb when ra == rb -> true
  | Some ra, _ when not (T.least ra) ->
      add (T.row_contents a) b = [] && link ra (beyond b a)
  | _, Some rb when not (T.least rb) ->
      add (T.row_contents b) a = [] && link rb (beyond a b)
  | Some ra, _ ->
      covers a b && add (T.row_contents a) b = [] && link ra (beyond b a)
  | None, Some rb ->
      covers b a && add (T.row_contents b) a = [] && link rb (beyond a b)
  | None, None -> add (T.row_contents a) b = [] && add (T.row_contents b) a = []

(* The row [r] without the labels that the row [m] writes itself: what the
   open variable that ends [m] stands for once [m] and [r] are one. So
   [{raise<E>, e}] and [{raise<Box>, r}] make [e] the row [r], not
   [{raise<Box>, r}]. *)
and beyond (r : T.row) (m : T.row) : T.row =
  {
    r with
    io = r.io && not m.io;
    raise = (if Option.is_some m.raise then None else r.raise);
    effects =
      List.filter (fun (e, _) -> not (List.mem_assoc e m.effects)) r.effects;
  }

(* Whether the row [outer] holds the effects that [inner] holds now. *)
and covers outer inner =
  let o = T.row_contents outer and i = T.row_contents inner in
  ((not i.io) || o.io)
  && (Option.is_none i.raise || Option.is_some o.raise)
  && List.for_all (fun (e, _) -> List.mem_assoc e o.effects) i.effects
  && List.for_all (holds (T.params outer)) (T.params inner)

(* Whether a row whose parameters are [ps] holds the parameter [p]. An
   implicit one that it lacks is no error of its own: it reaches the row only
   through a parameter that escapes, which phase 2 reports (effects.escaping-parameters). *)
and holds ps (p : T.row_param) = p.implicit || T.has_param ps p

(* Makes the open row [rv] the row [r], which already holds its effects, and
   moves its upper bounds to [r]. A row can't hold itself (types.infinite-types). *)
and link rv r =
  (not (T.row_mentions rv r))
  &&
  let uppers = T.uppers rv in
  T.set_row_state rv (Link r);
  List.for_all (fun (upper, handled) -> fit ~handled r upper = []) uppers

(* Makes the effects of [actual] part of [expected], now and as [actual]
   grows, and returns what [expected] can't hold (effects.inference and effects.function-values). A
   raise that [handled] catches, as a [try … catch] does, must have its type,
   and doesn't reach [expected], and neither does an effect that a [with]
   handles, whose arguments must be the handler's (handlers.with). *)
and fit ?(handled = T.Nothing) actual expected =
  let a = T.row_contents actual in
  let a, handled_problems =
    match (handled, a.raise) with
    | Raise_of h, Some u ->
        ( { a with raise = None },
          if unify u h then [] else [ Raise_mismatch (u, h) ] )
    | Effect_of (e, args), _ -> (
        match List.assoc_opt e a.effects with
        | Some given ->
            ( T.without_effect e a,
              if unify_all given args then []
              else [ Effect_mismatch (e, given, args) ] )
        | None -> (a, []))
    | _ -> (a, [])
  in
  (match (open_var actual, open_var expected) with
  | Some ra, Some re when ra == re -> ()
  | Some ra, _ -> T.add_upper ra (expected, handled)
  | None, _ -> ());
  handled_problems @ add a expected

(* Adds the effects [a], whose tail is closed or a row parameter, to a row:
   an open row grows to hold them, and any other row must hold them
   already. *)
and add (a : T.row) expected =
  (* effects.error-type-raises: a raise of the error type fits every row. *)
  let a =
    match Option.map T.resolve a.raise with
    | Some Error -> { a with raise = None }
    | _ -> a
  in
  let e = T.row_contents expected in
  let raise_problems =
    match (a.raise, e.raise) with
    | Some u, Some t -> if unify u t then [] else [ Raise_mismatch (u, t) ]
    | Some u, None when Option.is_none (open_var expected) ->
        [ Missing_raise u ]
    | Some _, None | None, _ -> []
  in
  (* handlers.effects-in-rows: an effect the row holds takes its arguments, and the
     open row holds the others. *)
  let effect_problems =
    List.filter_map
      (fun (eff, args) ->
        match List.assoc_opt eff e.effects with
        | Some held when unify_all args held -> None
        | Some held -> Some (Effect_mismatch (eff, args, held))
        | None when Option.is_some (open_var expected) -> None
        | None -> Some (Missing_effect eff))
      a.effects
  in
  let a =
    {
      a with
      effects =
        List.filter
          (fun (eff, _) -> not (List.mem_assoc eff e.effects))
          a.effects;
    }
  in
  raise_problems @ effect_problems
  @
  match open_var expected with
  | Some rv -> grow rv a ~declared:e.raise
  | None ->
      (if a.io && not e.io then [ Missing_io ] else [])
      @ List.filter_map
          (fun (p : T.row_param) ->
            if holds (T.params e) p then None else Some (Missing_var p.var))
          (T.params a)

(* Grows the open row [rv] by the effects [a] it lacks, and passes what it
   gains on to its upper bounds. [declared] is the raise the whole row already
   has. *)
and grow rv (a : T.row) ~declared =
  let lower =
    match T.row_state rv with
    | Open lower -> lower
    | Link _ -> invalid_arg "Check_unify.grow"
  in
  let raise, raise_problems =
    match (declared, a.raise) with
    | None, Some u when T.row_occurs rv u -> (None, [ Cyclic_raise u ])
    | None, Some u -> (Some u, [])
    | (Some _ | None), _ -> (None, [])
  in
  let new_params =
    List.filter (fun p -> not (T.has_param (T.params lower) p)) (T.params a)
  in
  let effects =
    List.filter (fun (e, _) -> not (List.mem_assoc e lower.effects)) a.effects
  in
  let gained =
    {
      T.io = a.io && not lower.io;
      raise;
      effects;
      tail = T.params_tail new_params;
    }
  in
  let grown =
    {
      T.io = lower.io || gained.io;
      raise = (match raise with Some _ -> raise | None -> lower.raise);
      effects = lower.effects @ effects;
      tail = T.params_tail (T.union_params (T.params lower) new_params);
    }
  in
  T.set_row_state rv (Open grown);
  let upper_problems =
    if gained.io || Option.is_some raise || new_params <> [] || effects <> []
    then
      List.concat_map
        (fun (upper, handled) -> fit ~handled gained upper)
        (T.uppers rv)
    else []
  in
  (* A raise that an upper bound rejects is reported where it comes, and the
     row doesn't keep it, so later code isn't checked against it. *)
  if
    List.exists
      (function Raise_mismatch _ -> true | _ -> false)
      upper_problems
  then T.set_row_state rv (Open { grown with raise = lower.raise });
  raise_problems @ upper_problems
