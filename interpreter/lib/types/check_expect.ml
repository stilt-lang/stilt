(* Expected types: requiring a type to be the one expected, and checking an
   expression against one. *)

module T = Types
open Check_state
open Check_unify

(* polymorphism.rigid-types: a rigid type given to a type inferred outside the
   expression checked with it would escape, since nothing outside knows what
   it is. *)
let escaped st loc (v : Hir.var) =
  error st Code.e0311 loc
    "`%s` stands for any type here, so it can't be given a type from outside \
     this function"
    v.name;
  false

let mismatch st loc ~expected actual =
  let hint =
    if show actual = show (T.option expected) then
      "; it is `None` when a value is missing, so give a fallback with `else`"
    else ""
  in
  match List.filter T.is_rigid (T.type_params actual) with
  | _ when Check_fresh.leaves st loc ~expected actual -> false
  | v :: _ when Option.is_some (T.unsolved expected) -> escaped st loc v
  | _ ->
      error st Code.e0311 loc "expected `%s`, found `%s`%s" (show expected)
        (show actual) hint;
      false

(* Requires [actual] to be [expected], and tells whether it is. *)
let agrees st loc ~expected actual =
  unify actual expected || mismatch st loc ~expected actual

let expect st loc ~expected actual = ignore (agrees st loc ~expected actual)

(* Requires a value of type [actual] to be usable where [expected] is, and
   tells whether it is: a value of type [Never] fits anywhere, and a function
   fits where a function type with a larger row is expected (declarations.never;
   effects.function-value-unions). *)
let fits st loc ~expected actual =
  match (T.resolve actual, T.resolve expected) with
  | a, _ when a = T.never -> true
  | Fn (ps, r, row), Fn (qs, s, row')
    when List.length ps = List.length qs
         && not (List.exists (fun (_, t) -> Packs.is_spread t) (ps @ qs)) ->
      List.for_all2 (fun (m, x) (n, y) -> m = n && unify y x) ps qs
      && unify r s
      && fit row row' = []
      || mismatch st loc ~expected actual
  | _ -> agrees st loc ~expected actual

let subsume st loc ~expected actual = ignore (fits st loc ~expected actual)

(* A type that values of type [t] fit in, whose function row may grow to
   hold the rows of other function values (effects.function-value-unions). *)
let widen t =
  match T.resolve t with
  | Fn (params, ret, _) -> T.Fn (params, ret, T.fresh_row ~least:true ())
  | t -> t

(* A type that must be known where it is used, as a receiver's is (traits.method-resolution). A literal's type takes its default there (numbers.literal-defaults). *)
let known st (loc : Ast.loc) t =
  if Option.is_some (T.unsolved t) then improve st;
  (match T.unsolved t with
  | Some { kind = Int_literal; _ } -> T.solve t T.i64
  | Some { kind = Float_literal; _ } -> T.solve t T.f64
  | _ -> ());
  match T.resolve t with
  | Error -> None
  | Var _ ->
      (match T.unsolved t with
      | Some v when (not v.tainted) && not (List.mem v.id st.unknown) ->
          st.unknown <- v.id :: st.unknown;
          error st Code.e0312 loc
            "the type of this expression must be known here; add an annotation"
      | _ -> ());
      None
  | t -> Some t

(* Infers the type of [e], as [Check_exprs.infer] does, checking it against
   [expected] where there is one. *)
let infer ctx expected e = ctx.infer ctx expected e

(* polymorphism.instantiation: a value of a polymorphic function type, used where none
   is expected, is instantiated afresh, as naming a generic function is. *)
let instantiated st expected (v : Tast.expr) =
  match (T.resolve v.ty, Option.map T.resolve expected) with
  | Forall _, Some (Forall _) -> v
  | Forall p, _ ->
      let args, ty = Check_types.instantiate_poly st v.loc p in
      node (Instantiate (v, args)) ty v.loc
  | _ -> v

(* polymorphism.rigid-types: the rigid type that the effects a function passes on
   hold, which would escape through its caller's row. *)
let raises_rigid rigid body =
  match T.resolve body with
  | Fn (_, _, row) ->
      Option.bind (T.row_contents row).raise (fun t ->
          List.find_opt (fun (v : Hir.var) -> T.mentions_param [ v ] t) rigid)
  | _ -> None

(* [check], telling whether [e] fits [expected]. *)
let rec check_fits ctx expected e =
  match T.resolve expected with
  | Forall p -> generalize ctx p e
  | _ ->
      let v = infer ctx (Some expected) e in
      (v, fits ctx.st e.loc ~expected v.ty)

(* polymorphism.rigid-types: where a polymorphic function type is expected, a generic
   function named as a value, or a closure literal, is checked with each of
   its type parameters a rigid type, which only its bounds are known of, as a
   function's own type parameter is in its body. Any other expression must
   have the same polymorphic function type (polymorphism.instantiation), or is E0311. *)
and generalize ctx (p : T.forall) (e : Hir.expr) =
  let st = ctx.st in
  match e.desc with
  | Func _ | Member _ | Closure _ ->
      let rigid =
        List.map
          (fun ((v : Hir.var), _) -> Env.synthetic ~loc:v.loc v.name)
          p.generics
      in
      let args = List.map T.rigid rigid in
      st.bounds <- List.combine rigid (T.instance_bounds p args) @ st.bounds;
      let body = T.instance p args in
      let v, ok = check_fits ctx body e in
      let ok =
        ok
        &&
        match raises_rigid rigid body with
        | Some r -> escaped st e.loc r
        | None -> true
      in
      (node (Generalize (rigid, v)) (T.Forall p) e.loc, ok)
  | _ ->
      let v = infer ctx (Some (T.Forall p)) e in
      (v, fits st e.loc ~expected:(T.Forall p) v.ty)

let check ctx expected e = fst (check_fits ctx expected e)

(* Checks an expression whose expected type an error hides, as the error
   type, so that it causes no error of its own (errors.error-type). *)
let abandon ctx e = check ctx T.Error e

(* Checks [e] against [expected] when there is one. *)
let infer_checked ctx expected e =
  match expected with Some t -> check ctx t e | None -> infer ctx None e

(* The type that the first branch of an [if], a [match] or a [try … catch]
   whose type isn't expected gives the later branches, which are checked against it (expressions.if). A function type's row grows to hold theirs (effects.function-value-unions).
   [None] while every branch so far has type [Never]. *)
let settled st ty loc =
  if is_never ty then None
  else
    let common = widen ty in
    subsume st loc ~expected:common ty;
    Some common
