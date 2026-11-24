(* Substitution of type parameters and row parameters, over the types of
   [Types_core]. *)

include Types_core

let rec subst types rows t =
  match resolve t with
  | Con (item, args) -> Con (item, List.map (subst types rows) args)
  | Param p -> (
      match List.find_opt (fun ((q : Hir.var), _) -> q.id = p.id) types with
      | Some (_, t) -> t
      | None -> Param p)
  | Tuple ts -> Tuple (subst_elems types rows ts)
  | Record fields ->
      Record (List.map (fun (f, t) -> (f, subst types rows t)) fields)
  | Spread (p, t) -> Spread (subst types rows p, subst types rows t)
  | App (h, args) ->
      apply (subst types rows h) (List.map (subst types rows) args)
  | Fn (params, ret, row) ->
      Fn
        ( List.concat_map
            (fun (m, t) ->
              List.map (fun t -> (m, t)) (subst_elems types rows [ t ]))
            params,
          subst types rows ret,
          subst_row types rows row )
  | Handler h ->
      Handler
        {
          h with
          hargs = List.map (subst types rows) h.hargs;
          answer = Option.map (subst types rows) h.answer;
          hrow = subst_row types rows h.hrow;
        }
  | Forall p ->
      let bound b = { b with args = List.map (subst types rows) b.args } in
      Forall
        {
          generics = List.map (fun (v, bs) -> (v, List.map bound bs)) p.generics;
          body = subst types rows p.body;
        }
  | (Var _ | Value _ | Error) as t -> t

(* variadics.type-spreads: elements, of a tuple or of a function type's parameters,
   where a spread of a pack that [types] replaces by a tuple stands for one
   element for each of its, with the pack replaced by the element. *)
and subst_elems types rows ts =
  List.concat_map
    (fun t ->
      match t with
      | Spread (pack, body) -> (
          match resolve pack with
          | Param v -> (
              match
                List.find_opt (fun ((q : Hir.var), _) -> q.id = v.id) types
              with
              | Some (_, by) -> spread_by types rows v by body
              | None -> [ subst types rows t ])
          | _ -> [ subst types rows t ])
      | t -> [ subst types rows t ])
    ts

and spread_by types rows v by body =
  match resolve by with
  | Tuple es ->
      List.map
        (function
          | Spread (q, b) -> Spread (q, subst ((v, b) :: types) rows body)
          | e -> subst ((v, e) :: types) rows body)
        (expand es)
  | _ -> [ Spread (by, subst types rows body) ]

(* Each row parameter that [rows] replaces gives way to its replacement,
   which gains the row's labels. At most one replacement may end in an open
   row, as [Check_types.instantiate] ensures. *)
and subst_row types rows r =
  let raise = Option.map (subst types rows) r.raise in
  let r = { r with effects = map_effects (subst types rows) r.effects } in
  match r.tail with
  | Row_params ps ->
      let replacement (p : row_param) =
        List.find_map
          (fun ((q : Hir.var), row) ->
            if q.id = p.var.id then Some row else None)
          rows
      in
      let kept = List.filter (fun p -> Option.is_none (replacement p)) ps in
      List.fold_left join
        { r with raise; tail = params_tail kept }
        (List.filter_map replacement ps)
  | Closed | Row_var _ -> { r with raise }

and join acc replacement =
  let tail =
    match (acc.tail, replacement.tail) with
    | tail, Closed | Closed, tail -> tail
    | Row_params ps, Row_params qs -> Row_params (union_params ps qs)
    | (Row_params _ | Row_var _), Row_var _ | Row_var _, Row_params _ ->
        invalid_arg "Types.subst_row"
  in
  { (merge_labels replacement acc) with tail }

let mentions_param vars t =
  List.exists
    (fun (p : Hir.var) -> List.exists (fun (v : Hir.var) -> v.id = p.id) vars)
    (type_params t)

(* polymorphism.instantiation: an instantiation of a polymorphic function type. *)
let instance_subst p args =
  List.map2 (fun ((v : Hir.var), _) t -> (v, t)) p.generics args

let instance p args = subst (instance_subst p args) [] p.body

let instance_bounds p args =
  let sub = subst (instance_subst p args) [] in
  List.map
    (fun (_, bs) ->
      List.map (fun b -> { b with args = List.map sub b.args }) bs)
    p.generics
