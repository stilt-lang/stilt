(* The types and signatures that declarations write, and when two of them
   are the same (traits.impl-signatures). *)

module T = Types
open Env_tables

(* Written types *)

let rec of_hir ?self (t : Hir.ty) =
  match t.desc with
  | Ty_con (item, args) -> T.Con (item, List.map (of_hir ?self) args)
  | Ty_param v -> T.Param v
  | Ty_self -> Option.value self ~default:T.Error
  (* traits.constructor-traits and traits.constructor-parameters *)
  | Ty_app (v, args) -> T.App (T.Param v, List.map (of_hir ?self) args)
  | Ty_self_app args ->
      T.apply
        (Option.value self ~default:T.Error)
        (List.map (of_hir ?self) args)
  | Ty_tuple ts -> T.Tuple (List.map (of_hir ?self) ts)
  (* records.anonymous-types *)
  | Ty_record fields ->
      T.record
        (List.map
           (fun (f : Hir.field_decl) -> (f.field.desc, of_hir ?self f.ty))
           fields)
  (* variadics.type-spreads *)
  | Ty_spread (v, t) -> T.Spread (T.Param v, of_hir ?self t)
  | Ty_fn (generics, params, ret, row) -> (
      let fn =
        T.Fn
          ( List.map (fun (mode, t) -> (mode, of_hir ?self t)) params,
            Option.fold ~none:T.unit ~some:(of_hir ?self) ret,
            of_hir_row ?self row )
      in
      (* polymorphism.function-types *)
      match generics with
      | [] -> fn
      | gs ->
          T.Forall
            {
              generics =
                List.map
                  (fun ({ var; bounds; _ } : Hir.type_param) ->
                    (var, bounds_of_refs ?self bounds))
                  gs;
              body = fn;
            })
  (* handlers.handler-types *)
  | Ty_handler (e, answer, row) ->
      T.Handler
        {
          eff = e.eff;
          hargs = List.map (of_hir ?self) e.args;
          answer = Option.map (of_hir ?self) answer;
          hrow = of_hir_row ?self row;
        }
  (* generics.constant-arguments *)
  | Ty_value v -> T.Value v
  | Ty_error -> T.Error

and bounds_of_refs ?self (bounds : Hir.bound list) =
  List.filter_map
    (fun ({ trait; args } : Hir.bound) ->
      match trait with
      | Hir.Trait_ref trait ->
          Some { trait; args = List.map (of_hir ?self) args }
      | Trait_error -> None)
    bounds

and of_hir_row ?self (r : Hir.row) : T.row =
  {
    io = r.io;
    raise = Option.map (of_hir ?self) r.raise;
    effects =
      List.map
        (fun (e : Hir.effect_inst) -> (e.eff, List.map (of_hir ?self) e.args))
        r.effects;
    tail =
      (match r.var with
      | Some var -> Row_params [ { var; implicit = false } ]
      | None -> Closed);
  }

(* Synthetic variables, whose ids no declaration has. *)
let synthetic =
  let next = ref 0 in
  fun ?(loc = { Ast.line = 0; col = 0 }) name ->
    decr next;
    { Hir.id = !next; name; loc }

let bounds_of ?self (params : Hir.type_param list) =
  List.map
    (fun ({ var; bounds; _ } : Hir.type_param) ->
      (var, bounds_of_refs ?self bounds))
    params

(* effects.non-escaping-parameters: a parameter of function type, neither [inout] nor
   written [escaping], passes its argument's effects through, as though its
   row held an implicit row variable of its own, which the function's own row
   holds too. Its type gains that variable, which the result lists. *)
let pass_through (p : Hir.param) (mode, t) =
  let implicit (v : Hir.var) params ret row =
    let rp = { T.var = synthetic ~loc:v.loc v.name; implicit = true } in
    let row = { row with T.tail = T.params_tail (T.params row @ [ rp ]) } in
    (T.Fn (params, ret, row), Some rp)
  in
  match (p, T.resolve t) with
  | Param (Let, v, _, false), Fn (params, ret, row) ->
      let t, rp = implicit v params ret row in
      ((mode, t), rp)
  (* polymorphism.effects-and-escaping: so does a parameter of a polymorphic function type. *)
  | Param (Let, v, _, false), Forall ({ body = Fn (params, ret, row); _ } as f)
    ->
      let body, rp = implicit v params ret row in
      ((mode, T.Forall { f with body }), rp)
  (* handlers.handler-types: so does a parameter of handler type, whose effects pass
     through to the caller. *)
  | Param (Let, v, _, false), Handler h ->
      let rp = { T.var = synthetic ~loc:v.loc v.name; implicit = true } in
      let hrow =
        { h.hrow with tail = T.params_tail (T.params h.hrow @ [ rp ]) }
      in
      ((mode, T.Handler { h with hrow }), Some rp)
  | _ -> ((mode, t), None)

(* The row of a function type, or of a polymorphic one's body. *)
let fn_row t =
  match T.resolve t with
  | T.Fn (_, _, row) | Forall { body = Fn (_, _, row); _ } -> Some row
  | Handler h -> Some h.hrow
  | _ -> None

let passing (s : fn_sig) =
  List.map
    (fun (_, t) ->
      match fn_row t with
      | Some row ->
          List.exists (fun (p : T.row_param) -> p.implicit) (T.params row)
      | None -> false)
    s.params

(* traits.where: the bounds of a function's [where] clause on its impl
   block's member types, which are type parameters of the block. *)
let where_assumed ?self (f : Hir.fn_decl) =
  List.filter_map
    (fun ((t : Hir.ty), (b : Hir.bound), _) ->
      match (of_hir ?self t, b.trait) with
      | (T.Param _ as t), Hir.Trait_ref trait ->
          Some (t, { trait; args = List.map (of_hir ?self) b.args })
      | _ -> None)
    f.where_bounds

(* The signature of a function, whose receiver has type [self_ty] and whose
   [Self] means [self]. *)
let signature ?self ?(self_ty = T.Error) ~outer (f : Hir.fn_decl) =
  let type_params =
    List.filter_map
      (function Hir.Type_param p -> Some p | Row_param _ -> None)
      f.generics
  in
  let row_params =
    List.filter_map
      (function Hir.Row_param v -> Some v | Type_param _ -> None)
      f.generics
  in
  let params, implicit =
    List.split
      (List.map
         (fun (p : Hir.param) ->
           pass_through p
             (match p with
             | Self_param (mode, _, None) -> (mode, self_ty)
             (* traits.receiver-types *)
             | Self_param (mode, _, Some t) -> (mode, of_hir ?self t)
             | Param (mode, _, t, _) -> (mode, of_hir ?self t)))
         f.params)
  in
  let implicit = List.filter_map Fun.id implicit in
  let row = of_hir_row ?self f.row in
  {
    type_params = outer @ bounds_of ?self type_params;
    row_params = row_params @ List.map (fun (p : T.row_param) -> p.var) implicit;
    params;
    ret = Option.fold ~none:T.unit ~some:(of_hir ?self) f.ret;
    projection = f.projection;
    assumed = where_assumed ?self f;
    row = { row with tail = T.params_tail (T.params row @ implicit) };
  }

(* Equality *)

let rec equal a b =
  match (T.resolve a, T.resolve b) with
  | T.Con (i, xs), T.Con (j, ys) -> i = j && equal_list xs ys
  | Param p, Param q -> p.id = q.id
  | App (f, xs), App (g, ys) -> equal f g && equal_list xs ys
  | Tuple xs, Tuple ys -> equal_list xs ys
  | Record xs, Record ys ->
      List.map fst xs = List.map fst ys
      && equal_list (List.map snd xs) (List.map snd ys)
  | Spread (p, x), Spread (q, y) -> equal p q && equal x y
  | Fn (ps, r, row), Fn (qs, s, row') ->
      List.length ps = List.length qs
      && List.for_all2 (fun (m, x) (n, y) -> m = n && equal x y) ps qs
      && equal r s && equal_row row row'
  | Forall p, Forall q -> (
      match renaming p q with
      | Some sub -> equal p.body (sub q.body)
      | None -> false)
  | Handler h, Handler k ->
      h.eff = k.eff && equal_list h.hargs k.hargs
      && (match (h.answer, k.answer) with
        | None, None -> true
        | Some x, Some y -> equal x y
        | _ -> false)
      && equal_row h.hrow k.hrow
  | Error, _ | _, Error -> true
  | _ -> false

and equal_list xs ys =
  List.length xs = List.length ys && List.for_all2 equal xs ys

and equal_row (a : T.row) (b : T.row) =
  a.io = b.io
  && (match (a.raise, b.raise) with
    | None, None -> true
    | Some x, Some y -> equal x y
    | _ -> false)
  && List.length a.effects = List.length b.effects
  && List.for_all
       (fun (e, args) ->
         match List.assoc_opt e b.effects with
         | Some others -> equal_list args others
         | None -> false)
       a.effects
  &&
  let ids r =
    List.sort compare
      (List.map (fun (p : T.row_param) -> p.var.id) (T.params r))
  in
  ids a = ids b

(* polymorphism.instantiation: two polymorphic function types are the same when they
   declare as many type parameters, with the same bounds in the same order,
   and are equal once the second's are renamed the first's. Gives that
   renaming. *)
and renaming (p : T.forall) (q : T.forall) =
  if List.length p.generics <> List.length q.generics then None
  else
    let names =
      List.map2 (fun (v, _) (w, _) -> (w, T.Param v)) p.generics q.generics
    in
    let sub = T.subst names [] in
    if
      List.for_all2
        (fun (_, a) (_, b) -> same_bounds Fun.id a (List.map (rename sub) b))
        p.generics q.generics
    then Some sub
    else None

and rename sub (b : bound) = { b with args = List.map sub b.args }

(* Whether two lists of bounds name the same traits with the same
   arguments, once [sub] renames the first's type parameters. *)
and same_bounds sub (a : bound list) (b : bound list) =
  let a =
    List.map (fun (x : bound) -> { x with args = List.map sub x.args }) a
  in
  let covers xs ys =
    List.for_all
      (fun (x : bound) ->
        List.exists
          (fun (y : bound) -> x.trait = y.trait && equal_list x.args y.args)
          ys)
      xs
  in
  covers a b && covers b a

(* traits.impl-signatures: whether an impl method's signature is the trait's, once
   [Self] is the impl's type, each trait parameter its argument (traits.trait-arguments), and the method's generics correspond in order. *)
let matches_trait ~self_param ~self_ty ~fixed (expected : fn_sig)
    (actual : fn_sig) ~own =
  let own_params = List.filteri (fun i _ -> i >= own) actual.type_params in
  List.length expected.type_params = List.length own_params
  && List.length expected.row_params = List.length actual.row_params
  &&
  let types =
    ((self_param, self_ty) :: fixed)
    @ List.map2
        (fun ((v : Hir.var), _) ((w : Hir.var), _) -> (v, T.Param w))
        expected.type_params own_params
  in
  let rows =
    List.map2
      (fun v var ->
        (* Only the ids of row parameters are compared. *)
        (v, { T.empty_row with tail = Row_params [ { var; implicit = false } ] }))
      expected.row_params actual.row_params
  in
  let sub = T.subst types rows in
  List.for_all2
    (fun (_, a) (_, b) -> same_bounds (T.subst types []) a b)
    expected.type_params own_params
  && List.length expected.params = List.length actual.params
  && List.for_all2
       (fun (m, a) (n, b) -> m = n && equal (sub a) b)
       expected.params actual.params
  && equal (sub expected.ret) actual.ret
  && expected.projection = actual.projection
  && equal_row (T.subst_row types rows expected.row) actual.row
