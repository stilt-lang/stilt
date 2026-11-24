open Model_types
open Model_forms

(* Projections in the Lean model's calculus. A projection's call is a place
   (projections.call-is-place), which the calculus lacks, so the export writes the
   caller's access to it as a closure literal, its access, and the projection as a
   function of its own for that access, whose [yield p] calls the access with [p]
   [inout] (projections.when-projection-runs). The projection's arguments, the other
   operands and the indexes of the place are evaluated first, in their order, into
   temporaries; the call then starts, runs its body to its [yield], where the access
   happens on the yielded place, resumes and ends, and its [inout] arguments are
   written back. An access that raises leaves the projection without resuming
   (projections.raising-during-access), as a call through it does. The other
   places of the access's call, and the places that projections before it in the
   call yield, are threaded through the projection as [inout] arguments of its own,
   since a closure captures by copy (expressions.capture). Projections that are
   arguments of one call start from left to right, each running inside the one
   before it. *)

let counter = ref (-1000)

let fresh name (t : Types.ty) (loc : Ast.loc) =
  decr counter;
  let v = { Hir.id = !counter; name; loc } in
  (v, { Tast.desc = Local v; ty = t; loc })

let unit_ty = Types.Tuple []
let list_of t = Types.Con (list_item, [ t ])
let stmt at s : Tast.stmt = { stmt = s; at }

let bind_pat (v : Hir.var) t : Tast.pattern =
  { pat = P_bind v; pty = t; ploc = v.loc }

(* An argument of a projection's call, evaluated: a value, or the [n]th place of those
   the access threads, which the call takes [inout]. *)
type harg = HValue of Tast.expr | HPlace of int

(* A projection's call that a place is rooted in, its arguments evaluated. *)
type hole = {
  callee : Tast.callee;
  targs : Types.ty list;
  args : harg list;
  types : Types.ty list;
  ty : Types.ty;
  loc : Ast.loc;
}

(* What evaluating an access's operands gives: the temporaries bound, in order, and the
   places threaded, by their positions. *)
type prepared = { lets : (Hir.var * Tast.expr) list; places : Tast.expr list }

let rec rooted (p : Tast.expr) =
  match p.desc with
  | Project _ -> true
  | Field (b, _) | Tuple_field (b, _) | Index (b, _) -> rooted b
  | _ -> false

let simple (e : Tast.expr) =
  match e.desc with Local _ | Int _ | Bool _ | Str _ -> true | _ -> false

(* An operand evaluated now into a temporary. *)
let hoist lets (e : Tast.expr) =
  if simple e then (lets, e)
  else
    let v, l = fresh "operand" e.ty e.loc in
    (lets @ [ (v, e) ], l)

(* A place rooted in a variable, its indexes evaluated now (values.index-reads). *)
let rec plain_place lets (p : Tast.expr) =
  match p.desc with
  | Local _ -> (lets, p)
  | Field (b, f) ->
      let lets, b = plain_place lets b in
      (lets, { p with desc = Field (b, f) })
  | Tuple_field (b, i) ->
      let lets, b = plain_place lets b in
      (lets, { p with desc = Tuple_field (b, i) })
  | Index (b, i) ->
      let lets, b = plain_place lets b in
      let lets, i = hoist lets i in
      (lets, { p with desc = Index (b, i) })
  | _ -> outside "a place the model lacks"

(* A place rooted in a projection's call: the call, its arguments evaluated, and the
   place rebuilt on the variable that stands for the yielded place. *)
let rec rooted_place (st : prepared) (p : Tast.expr) =
  let extend b make =
    let st, h, rebuild = rooted_place st b in
    (st, h, fun x -> { p with desc = make (rebuild x) })
  in
  match p.desc with
  | Project (callee, targs, args, _) ->
      let one (st, done_) (a : Tast.arg) =
        match a.mode with
        | Let ->
            let lets, v = hoist st.lets a.value in
            ({ st with lets }, done_ @ [ HValue v ])
        | Inout when rooted a.value ->
            outside "a projection's call as a projection's argument"
        | Inout ->
            let lets, v = plain_place st.lets a.value in
            let n = List.length st.places in
            ({ lets; places = st.places @ [ v ] }, done_ @ [ HPlace n ])
      in
      let st, hargs = List.fold_left one (st, []) args in
      let types = List.map (fun (a : Tast.arg) -> a.value.ty) args in
      ( st,
        { callee; targs; args = hargs; types; ty = p.ty; loc = p.loc },
        fun x -> x )
  | Field (b, f) -> extend b (fun b -> Field (b, f))
  | Tuple_field (b, i) -> extend b (fun b -> Tuple_field (b, i))
  | Index (b, i) ->
      let st, h, rebuild = rooted_place st b in
      let lets, i = hoist st.lets i in
      ({ st with lets }, h, fun x -> { p with desc = Index (rebuild x, i) })
  | _ -> outside "a place the model lacks"

let ty_key cx t = Model_json.to_string (ty cx t)

(* The union of two rows without row parameters (effects.rows). *)
let union cx (a : Types.row) (b : Types.row) : Types.row =
  let a = Types.row_contents a and b = Types.row_contents b in
  (match (a.tail, b.tail) with
  | Closed, Closed -> ()
  | _ -> outside "a projection whose access passes a row parameter on");
  let raise =
    match (a.raise, b.raise) with
    | None, r | r, None -> r
    | Some x, Some y when ty_key cx x = ty_key cx y -> Some x
    | _ -> outside "a projection whose access raises another error"
  in
  let key (e, args) =
    item_name e ^ String.concat "," (List.map (ty_key cx) args)
  in
  let mine = List.map key a.effects in
  let effects =
    a.effects @ List.filter (fun e -> not (List.mem (key e) mine)) b.effects
  in
  { io = a.io || b.io; raise; effects; tail = Closed }

let target_of cx (c : Tast.callee) =
  match c with
  | Function i -> Function i
  | Member (o, n) -> Member (o, n)
  | Trait_method (t, n, self) -> (
      match norm self with
      | Con (owner, _) when Model_fns.code cx (Impl (t, owner, n)) <> None ->
          Impl (t, owner, n)
      | _ -> outside "a projection of a trait at a type without code")
  | Operation _ -> outside "an operation as a projection"

(* The projection written for an access of the type [kty], which threads [extras]:
   a function of its own, written once, and the call's type arguments and row. *)
let written cx (h : hole) extras kty result krow =
  let target = target_of cx h.callee in
  let s = Model_fns.signature cx target in
  let d, _ =
    match Model_fns.code cx target with
    | Some c -> c
    | None ->
        outside "the projection %s, which has no code"
          (Model_fns.target_name target)
  in
  let row = union cx s.row krow in
  let item =
    {
      Hir.home = "model.projection";
      name = Model_fns.target_name target ^ " for " ^ ty_key cx kty;
    }
  in
  if not (List.mem_assoc item cx.projections) then begin
    let xs = List.map (fun t -> fresh "threaded" t d.at) extras in
    let kv, k = fresh "access" kty d.at in
    let res, _ = fresh "yielded" (list_of result) d.at in
    let s' =
      {
        s with
        params =
          s.params
          @ List.map (fun t -> (Ast.Inout, t)) extras
          @ [ (Ast.Let, kty) ];
        ret = result;
        projection = false;
        row;
      }
    in
    let d' =
      {
        d with
        params =
          d.params
          @ List.map (fun (v, _) -> (Ast.Inout, v)) xs
          @ [ (Ast.Let, kv) ];
      }
    in
    let access = { res = var_name res; result; k; extras = List.map snd xs } in
    cx.projections <- (item, (s', d', access)) :: cx.projections
  end;
  (item, Model_fns.impl_args cx target h.targs h.types s @ h.targs, row)

let inout value : Tast.arg = { mode = Inout; value }

(* The calls of the projections [holes], each inside the one before it, the
   innermost doing [finish] with the variables of the yielded places and of the
   threaded ones, [plain] by their positions; its value is the access's, of type
   [result]. A projection takes its own places [inout], and threads the others. *)
let rec nest cx loc holes xs plain finish result krow =
  match holes with
  | [] -> (finish xs plain, krow)
  | (h : hole) :: rest ->
      let own =
        List.filter_map
          (function HPlace n -> Some n | HValue _ -> None)
          h.args
      in
      let others = List.filter (fun (n, _) -> not (List.mem n own)) plain in
      let ctx = xs @ List.map snd others in
      let xv, x = fresh "place" h.ty loc in
      let es =
        List.map (fun (c : Tast.expr) -> fresh "threaded" c.ty loc) ctx
      in
      let renamed = List.map snd es in
      let k_xs = List.filteri (fun i _ -> i < List.length xs) renamed in
      let k_plain =
        List.map2
          (fun (n, _) e -> (n, e))
          others
          (List.filteri (fun i _ -> i >= List.length xs) renamed)
      in
      let body, body_row =
        nest cx loc rest (k_xs @ [ x ]) k_plain finish result krow
      in
      let types = List.map (fun (c : Tast.expr) -> c.ty) ctx in
      let kty =
        Types.Fn
          ( (Ast.Inout, h.ty) :: List.map (fun t -> (Ast.Inout, t)) types,
            result,
            body_row )
      in
      let pats =
        bind_pat xv h.ty
        :: List.map (fun (v, (c : Tast.expr)) -> bind_pat v c.ty) es
      in
      let k = { Tast.desc = Closure (pats, [], body); ty = kty; loc } in
      let item, targs, row = written cx h types kty result body_row in
      let arg = function
        | HValue v -> { Tast.mode = Let; value = v }
        | HPlace n -> inout (List.assoc n plain)
      in
      let args =
        List.map arg h.args @ List.map inout ctx
        @ [ { Tast.mode = Let; value = k } ]
      in
      ({ desc = Call (Function item, targs, args, row); ty = result; loc }, row)

let positions places = List.mapi (fun n p -> (n, p)) places

let wrapped loc lets (e : Tast.expr) =
  let let_ ((v : Hir.var), (x : Tast.expr)) =
    stmt loc
      (Let
         {
           pattern = bind_pat v x.ty;
           written = None;
           value = x;
           otherwise = None;
         })
  in
  { e with desc = Block (List.map let_ lets @ [ stmt loc (Expr e) ]) }

(* A read of a projection's call: the yielded place's value, copied out. *)
let read cx (e : Tast.expr) =
  let st, h, _ = rooted_place { lets = []; places = [] } e in
  let call, _ =
    nest cx e.loc [ h ] [] (positions st.places)
      (fun xs _ -> List.hd xs)
      e.ty Types.empty_row
  in
  wrapped e.loc st.lets call

(* [target = v], or [target op= v], where the target is rooted in a projection's call:
   the projection's arguments, the target's indexes, then the value
   (values.assignment-order). *)
let assign cx loc o (target : Tast.expr) (v : Tast.expr) =
  let st, h, rebuild = rooted_place { lets = []; places = [] } target in
  let lets, v = hoist st.lets v in
  let finish xs _ =
    {
      Tast.desc = Block [ stmt loc (Assign (o, rebuild (List.hd xs), v)) ];
      ty = unit_ty;
      loc;
    }
  in
  let call, _ =
    nest cx loc [ h ] [] (positions st.places) finish unit_ty Types.empty_row
  in
  wrapped loc lets call

type part =
  | Value of Tast.expr
  | Plain of int
  | Hole of hole * (Tast.expr -> Tast.expr)

let has_hole (args : Tast.arg list) =
  List.exists (fun (a : Tast.arg) -> a.mode = Inout && rooted a.value) args

(* A call with an [inout] argument rooted in a projection's call: its operands evaluated
   in order, then the projections' calls, the call itself the innermost access. *)
let call cx (e : Tast.expr) lets args krow remake =
  let one (st, parts) (a : Tast.arg) =
    match a.mode with
    | Let ->
        let lets, v = hoist st.lets a.value in
        ({ st with lets }, parts @ [ Value v ])
    | Inout when rooted a.value ->
        let st, h, rebuild = rooted_place st a.value in
        (st, parts @ [ Hole (h, rebuild) ])
    | Inout ->
        let lets, p = plain_place st.lets a.value in
        let n = List.length st.places in
        ({ lets; places = st.places @ [ p ] }, parts @ [ Plain n ])
  in
  let st, parts = List.fold_left one ({ lets; places = [] }, []) args in
  let holes =
    List.filter_map (function Hole (h, _) -> Some h | _ -> None) parts
  in
  let finish xs plain =
    let rec go parts xs =
      match (parts, xs) with
      | [], _ -> []
      | Value v :: rest, _ -> { Tast.mode = Let; value = v } :: go rest xs
      | Plain n :: rest, _ -> inout (List.assoc n plain) :: go rest xs
      | Hole (_, r) :: rest, x :: xs -> inout (r x) :: go rest xs
      | _ -> outside "a projection's call the model lacks"
    in
    { e with desc = remake (go parts xs) }
  in
  let call, _ = nest cx e.loc holes [] (positions st.places) finish e.ty krow in
  wrapped e.loc st.lets call

let fn_row (t : Types.ty) =
  match norm t with
  | Fn (_, _, r) -> r
  | _ -> outside "a call of a value the model lacks"

(* An expression with a projection's call where a place is, written in the calculus's
   terms; any other, as it is. *)
let desugar cx (e : Tast.expr) =
  match e.desc with
  | Project _ -> read cx e
  | Call (c, ts, args, row) when has_hole args ->
      call cx e [] args row (fun args -> Call (c, ts, args, row))
  | Call_value (f, args) when has_hole args ->
      let lets, f = hoist [] f in
      call cx e lets args (fn_row f.ty) (fun args -> Call_value (f, args))
  | _ -> e
