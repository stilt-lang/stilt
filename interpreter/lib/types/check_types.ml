(* The types of a body: the signatures it instantiates, and the types it
   writes and names. *)

module T = Types
module A = Tast
open Check_state
open Check_unify

(* effects.paired-row-variables: the row variables that a signature pairs with an error
   type, with that type, and effects.passing-to-paired-variables and effects.what-paired-variable-may-raise as handlers.with-pairing applies
   them, with each effect that a row holds beside them. A row of the
   signature is one of its parameter types' rows, at any depth, or its own
   row, with the implicit variables of its non-escaping parameters (effects.non-escaping-parameters). *)
let pairs (s : Env.fn_sig) =
  let rec of_ty acc = function
    | T.Fn (params, ret, row) ->
        List.fold_left
          (fun acc (_, t) -> of_ty acc t)
          (of_row (of_ty acc ret) row)
          params
    | Handler h ->
        List.fold_left of_ty (of_row acc h.hrow)
          (h.hargs @ Option.to_list h.answer)
    | Con (_, args) | Tuple args | App (_, args) ->
        List.fold_left of_ty acc args
    | Record fields -> List.fold_left of_ty acc (List.map snd fields)
    | Spread (_, t) -> of_ty acc t
    | Forall p -> of_ty acc p.body
    | Param _ | Var _ | Value _ | Error -> acc
  and of_row acc (row : T.row) =
    match T.row_contents row with
    | { raise; effects; tail = Row_params ps; _ } ->
        let labels =
          Option.to_list (Option.map (fun e -> A.Raise_label e) raise)
          @ List.map (fun (e, args) -> A.Effect_label (e, args)) effects
        in
        List.concat_map
          (fun (p : T.row_param) -> List.map (fun l -> (p.var, l)) labels)
          ps
        @ acc
    | _ -> acc
  in
  List.fold_left (fun acc (_, t) -> of_ty acc t) (of_row [] s.row) s.params

(* The function's own row at a use, whose row variables [rows] replaces with
   open rows. Two or more of them are joined into one open row that each
   reaches, since a row ends in at most one (effects.non-escaping-parameters). *)
let instantiate_row all rows (r : T.row) =
  match r.tail with
  | Row_params (_ :: _ :: _ as ps) ->
      let joined = T.fresh_row () in
      List.iter
        (fun (p : T.row_param) ->
          List.iter
            (fun ((v : Hir.var), row) ->
              if v.id = p.var.id then
                Option.iter
                  (fun rv -> T.add_upper rv (joined, Nothing))
                  (open_var row))
            rows)
        ps;
      { (T.subst_row all [] { r with tail = Closed }) with tail = joined.tail }
  | _ -> T.subst_row all rows r

(* The type arguments of an instance whose parameters hold the error type,
   which nothing may then decide, are tainted, so that no use of it is
   reported (errors.error-type). *)
let taint_broken types params =
  if List.exists (fun (_, t) -> T.mentions_error t) params then
    List.iter (fun (_, m) -> T.taint m) types

(* A signature at a use: its type parameters replaced by fresh variables,
   which meet their bounds, with the arguments they give (traits.bound-arguments),
   and [Self] and the trait's parameters by what [self] and [fixed] give. *)
let instantiate ?(fixed = []) st loc (s : Env.fn_sig) ~self ~use_at =
  let types =
    List.map (fun ((v : Hir.var), _) -> (v, fresh st loc)) s.type_params
  in
  let rows = List.map (fun v -> (v, T.fresh_row ())) s.row_params in
  let all =
    (match self with Some (v, t) -> [ (v, t) ] | None -> []) @ fixed @ types
  in
  let sub = T.subst all rows in
  List.iter2
    (fun ((v : Hir.var), bounds) (_, m) ->
      (* variadics.packs: a pack's bounds hold for each of its elements. *)
      let pack = Env.is_pack st.env v in
      List.iter
        (fun (b : Env.bound) ->
          obligation st (if pack then T.Spread (m, m) else m) b.trait loc;
          if not pack then fix st m b.trait (List.map sub b.args) loc)
        bounds;
      (* records.record-bounds *)
      Option.iter
        (fun fields ->
          require_fields st
            (if pack then T.Spread (m, m) else m)
            (List.map (fun (f, t) -> (f, sub t)) fields)
            loc)
        (Env.record_bound st.env v))
    s.type_params types;
  (* traits.where *)
  List.iter
    (fun (t, (b : Env.bound)) ->
      obligation st (sub t) b.trait loc;
      fix st (sub t) b.trait (List.map sub b.args) loc)
    s.assumed;
  (* effects.passing-to-paired-variables: what the use gives the variables the signature pairs.
     effects.what-paired-variable-may-raise: what it gives may raise only the paired type. *)
  List.iter
    (fun ((v : Hir.var), label) ->
      let row = List.assq v rows in
      match label with
      | A.Raise_label e ->
          Option.iter
            (fun rv ->
              T.add_upper rv
                ({ (T.fresh_row ()) with raise = Some (sub e) }, Nothing))
            (open_var row);
          st.passed <- (use_at, row, A.Raise_label (sub e)) :: st.passed
      | Effect_label (e, args) ->
          st.passed <-
            (use_at, row, A.Effect_label (e, List.map sub args)) :: st.passed)
    (pairs s);
  let params = List.map (fun (m, t) -> (m, sub t)) s.params in
  taint_broken types params;
  (List.map snd types, params, sub s.ret, instantiate_row all rows s.row)

(* polymorphism.instantiation: a polymorphic function type at a use, its type
   parameters replaced by fresh variables, which meet their bounds there. *)
let instantiate_poly st loc (p : T.forall) =
  let args = List.map (fun _ -> fresh st loc) p.generics in
  List.iter2
    (fun m bounds ->
      List.iter
        (fun (b : T.bound) ->
          obligation st m b.trait loc;
          fix st m b.trait b.args loc)
        bounds)
    args (T.instance_bounds p args);
  (args, T.instance p args)

(* A type constructor applied to fresh variables, and the variables. *)
let instantiate_type st loc item =
  match Env.type_info st.env item with
  | Some info ->
      let args = List.map (fun _ -> fresh st loc) info.params in
      (T.Con (item, args), args, info)
  | None -> (T.Error, [], { Env.params = []; def = Builtin; pub = true })

(* A type written in the body. An error in it is an error of the body
   (errors.error-type). *)
let of_hir st t =
  let ty = Env.of_hir ?self:st.self t in
  if T.mentions_error ty then st.broken <- true;
  ty

(* A type named in an expression or a pattern, whose arguments inference
   supplies (declarations.type-arguments). *)
let named_type st (hty : Hir.ty) =
  match hty.desc with
  | Ty_con (item, []) ->
      let ty, _, _ = instantiate_type st hty.loc item in
      ty
  | _ -> of_hir st hty
