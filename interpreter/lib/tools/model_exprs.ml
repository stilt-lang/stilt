open Model_json
open Model_types
open Model_ops
open Model_forms
open Model_natives

let writable cx (v : Hir.var) = List.mem v.id cx.writable

let rec expr cx (e : Tast.expr) =
  let e =
    Model_projections.desugar cx (Model_views.desugar ~writable:(writable cx) e)
  in
  match e.desc with
  | Int text when decimal_at_float e.ty text -> float_lit e.ty text
  | Unary (Neg, { desc = Int text; _ }) when decimal_at_float e.ty text ->
      unary Neg e.ty (float_lit e.ty text)
  | Int text -> int_lit e.ty text ~negated:false
  | Unary (Neg, { desc = Int text; _ }) -> int_lit e.ty text ~negated:true
  | Str s -> str_lit s
  | Bool b -> tag "bool" [ Bool b ]
  | Local v -> tag "var" [ Str (var_name v) ]
  | Interpolated segs -> op (Str "concat") (List.map (segment cx) segs)
  | Tuple [] -> unit_e
  | Tuple es -> op (Str "tuple") (List.map (expr cx) es)
  | Record (i, _, fields) when declared_record i ->
      let field (f, x) = Arr [ Str f; expr cx x ] in
      tag "record" [ Str (record_name cx e.ty); Arr (List.map field fields) ]
  | Construct (c, _, args) ->
      let t, name = ctor cx c e.ty in
      tag "variant" [ Str t; Str name; Arr (List.map (expr cx) args) ]
  | List es -> tag "list" [ ty cx (elem e.ty); Arr (List.map (expr cx) es) ]
  | Field (b, f) -> tag "field" [ expr cx b; Str f ]
  | Tuple_field (b, i) -> tag "field" [ expr cx b; Str (string_of_int i) ]
  | Index (b, k) when is_map b.ty -> map_op "index" [ expr cx b; expr cx k ]
  | Index (b, i) -> tag "index" [ expr cx b; expr cx i ]
  | Call (callee, targs, args, _) -> call cx e callee targs args
  | Call_value (f, args) -> call_value cx f args e.ty
  | Unary (_, x) when is_never x.ty ->
      (* declarations.never: an operand that never gives a value leaves the operator
         nothing to apply to, as in [-return x]. *)
      expr cx x
  | Unary (u, x) -> unary u x.ty (expr cx x)
  | Binary (b, x, y) when structural_cmp cx b x.ty -> (
      let pair (t, cs) = Arr [ Str t; Arr (List.map (fun c -> Str c) cs) ] in
      let orders = Arr (List.map pair (ctor_orders cx x.ty)) in
      match cmp b with
      | Some c ->
          op (tag "structural" [ Str c; orders ]) [ expr cx x; expr cx y ]
      | None -> outside "an operator")
  | Binary (b, x, y) when Model_traits.composed_at cx b x.ty ->
      Model_traits.composed_binary cx e b x.ty (expr cx x) (expr cx y)
  | Binary (b, x, y) when Model_traits.through_written cx b x.ty ->
      Model_traits.operator cx b (x.ty, expr cx x) (y.ty, expr cx y)
  | Binary (b, x, y) -> binary_at cx b x.ty y.ty (expr cx x) (expr cx y)
  | Closure (ps, _, body) -> closure cx e ps body
  | Block b -> block cx b
  | Comptime x -> expr cx x
  | _ -> control cx e

(* [==] and the ordering operators on a type other than the numeric types,
   [bool] and [str], through the prelude's structural impls (traits.operators). *)
and structural_cmp cx b t =
  let scalar =
    int_kind t <> None
    || float_kind t <> None
    ||
    match norm t with
    | Con ({ home = "std.prelude"; name = "bool" | "str" }, []) -> true
    | _ -> false
  in
  match cmp b with
  | Some ("eq" | "ne") when not scalar -> structural_by cx "Eq" t
  | Some _ when not scalar -> structural_by cx "Ord" t
  | _ -> false

and control cx (e : Tast.expr) =
  let otherwise = function None -> unit_e | Some x -> expr cx x in
  match e.desc with
  | If (c, b, o) -> tag "if" [ expr cx c; ty cx e.ty; block cx b; otherwise o ]
  | If_let (p, x, b, o) ->
      let wild = Arr [ Str "wild"; Arr []; otherwise o ] in
      tag "match" [ expr cx x; ty cx e.ty; Arr [ arm cx p (block cx b); wild ] ]
  | Match (x, arms) -> Model_match.match_e ~expr:(expr cx) cx e x arms
  | For (p, it, b) -> for_loop cx e p it b
  | Raise x -> tag "raise" [ expr cx x ]
  | Try (x, None) -> tag "try" [ expr cx x ]
  | Try (x, Some c) ->
      let error = { Hir.id = -1; name = "error"; loc = e.loc } in
      let scrutinee = tag "var" [ Str (var_name error) ] in
      let handler =
        Model_match.guarded ~expr:(expr cx) cx e.ty scrutinee c.arms
      in
      tag "tryCatch"
        [ expr cx x; ty cx c.error; Str (var_name error); handler; ty cx e.ty ]
  | While (c, b) -> tag "while" [ expr cx c; block cx b ]
  | Loop b -> tag "loop" [ block cx b ]
  | Break -> Str "break"
  | Continue -> Str "continue"
  | Return x -> tag "return" [ returned cx x ]
  | Float text -> float_lit e.ty text
  | Constant _ | Member_constant _ -> expr cx (constant cx e)
  | Value_param _ | Trait_constant _ -> outside "a constant"
  | Callee (Function i, targs) when Model_fns.code cx (Function i) <> None ->
      Model_fns.value cx i targs
  | Callee (c, ts) -> eta_closure cx e (fun a r -> Tast.Call (c, ts, a, r))
  | Constructor (i, ts) ->
      eta_closure cx e (fun a _ ->
          Tast.Construct (i, ts, List.map (fun (a : Tast.arg) -> a.value) a))
  | Generalize _ | Instantiate _ -> outside "a function as a value"
  | Update (base, fields) ->
      Model_records.update ~expr:(expr cx) cx e base fields
  | Spread _ | Record _ | Construct _ ->
      outside "a generic type's value, or an update"
  | Call _ | Project _ -> outside "a generic call or a projection"
  | Else (x, d) ->
      (* expressions.option-fallback: the value inside a [Some], or [d]. *)
      let v = temp "else" e.loc in
      let some =
        Arr
          [
            option_pattern cx x.ty [ tag "bind" [ Str v ] ];
            Arr [ Str v ];
            var_e v;
          ]
      in
      let none = Arr [ Str "wild"; Arr []; expr cx d ] in
      tag "match" [ expr cx x; ty cx e.ty; Arr [ some; none ] ]
  | Handler _ | With _ | Resume _ -> Model_handlers.form (handlers cx) cx e
  | When (pairs, b) -> Model_shared.when_ (shared cx) cx e pairs b
  | Error ->
      (* program.bodies-with-errors: code with an error panics where it is reached. *)
      op (tag "panic" [ Str "checkError" ]) []
  | Reflect _ | Quote _ | Hole -> outside "reflection, a quote or a hole"
  | _ -> outside "an expression the model lacks"

(* A constant's value, a constant expression of literals, tuples, lists,
   records and variants (declarations.constant-expressions), stands where it is
   read: evaluating it there gives the value, and the panic of a unary [-] that
   overflows at its first use (declarations.constant-evaluation). *)
(* A [for] over a list, or over the list of the integers a range yields
   (expressions.range-iteration), each element matched against the loop's
   pattern. *)
and for_loop cx (e : Tast.expr) (p : Tast.pattern) it b =
  let iterable, elem_ty =
    match it with
    | Iter it when is_map it.ty -> (
        (* expressions.for-iterables: a map yields its pairs in insertion
           order, which are its entries (std.maps). *)
        match norm it.ty with
        | Con (_, [ k; v ]) ->
            (map_op "entries" [ expr cx it ], Types.Tuple [ k; v ])
        | _ -> outside "an iteration over something other than a list")
    | Iter it -> (expr cx it, elem it.ty)
    | Range (a, z, fin) ->
        let incl = fin = Ast.Inclusive in
        let range = tag "list" [ tag "range" [ Bool incl ] ] in
        (op range [ expr cx a; expr cx z ], p.pty)
  in
  let body = block cx b in
  let name, body =
    match p.pat with
    | P_bind v -> (var_name v, body)
    | _ ->
        let n = temp "for" e.loc in
        (n, tag "match" [ var_e n; ty cx (block_ty b); Arr [ arm cx p body ] ])
  in
  tag "for" [ Str name; ty cx elem_ty; iterable; body ]

and segment cx = function
  | Tast.Text s -> str_lit s
  | Splice (x, None) -> Model_traits.shown cx x.ty (expr cx x)
  | Splice (x, Some spec) ->
      let v = expr cx x in
      formatted ~shown:(fun () -> Model_traits.shown cx x.ty v) x.ty spec v

and call cx (e : Tast.expr) callee targs args =
  match (callee : Tast.callee) with
  | Function i -> function_call cx e i targs args
  | Member (owner, name) when Model_shared.owns owner ->
      Model_shared.member_call (shared cx) cx e owner name args
  | Member (owner, name) when owner = Model_views.view_item ->
      Model_views.call ~writable:(writable cx) ~expr:(expr cx) e name args
  | Member (owner, name) when gives_option owner name e.ty ->
      option_call cx e owner name
        (List.map (fun (a : Tast.arg) -> expr cx a.value) args)
  | Member ({ home = "std.lazy"; name = "Lazy" }, name) -> (
      (* polymorphism.lazy-values: [new(f)] is [f], and [l.get()] calls it. *)
      match (name, args) with
      | "new", [ f ] -> expr cx f.value
      | "get", [ l ] -> call_value cx l.value [] e.ty
      | _ -> outside "the function std.lazy.Lazy.%s" name)
  | Member ({ home = "std.prelude"; name = "Set" }, name)
    when List.mem name Model_lists.set_natives ->
      Model_lists.set_call (callbacks cx) name args
  | Member (owner, name)
    when owner = map_item && List.mem name Model_lists.map_natives ->
      Model_lists.map_call (callbacks cx) cx e name args
  | Member ({ home = "std.array"; name = "Array" }, "len") ->
      Model_lists.list_call (callbacks cx) cx e "len" args
  | Member ({ home = "std.array"; name = "Array" }, "to_list") -> (
      (* generics.arrays: the elements in order, which the array's list is. *)
      match args with
      | [ a ] -> expr cx a.value
      | _ -> outside "the function std.array.Array.to_list")
  | Member (owner, name)
    when owner = list_item && List.mem name Model_lists.natives ->
      Model_lists.list_call (callbacks cx) cx e name args
  | Member (owner, name) when Model_fns.code cx (Member (owner, name)) <> None
    ->
      code_call cx e (Member (owner, name)) targs args
  | Member (owner, name) ->
      native owner name e.ty
        (List.map (fun (a : Tast.arg) -> expr cx a.value) args)
  | Trait_method (t, name, self) -> trait_call cx e t name self targs args
  | Operation (eff, name) ->
      Model_handlers.perform (handlers cx) cx e eff name targs args

(* A call of a function by its name: the natives of std that the calculus writes in its
   own terms, and a function with code. *)
and function_call cx (e : Tast.expr) (i : Hir.item) targs args =
  let exported () = List.map (fun (a : Tast.arg) -> expr cx a.value) args in
  match (Model_natives.std_call cx e i exported, i) with
  | Some call, _ -> call
  | None, i when Model_writes.owns i ->
      Model_writes.call (writing cx) cx e i args
  | None, { home = "std.task" | "std.par"; _ } ->
      Model_shared.std_call (shared cx) cx e i args
  | None, { home = "std.array"; name = "fill" } -> (
      match args with
      | [ x ] -> Model_lists.array_fill (callbacks cx) cx e x.value
      | _ -> outside "the function std.array.fill")
  | None, { home = "std.array"; name = "from_list" } -> (
      match args with
      | [ l ] -> Model_lists.array_from_list (callbacks cx) cx e l.value
      | _ -> outside "the function std.array.from_list")
  | None, _ when Model_fns.code cx (Function i) <> None ->
      code_call ~maps:true cx e (Function i) targs args
  | None, _ -> outside "the function %s" (item_name i)

(* A call of a trait's method at a known [Self]: the impl's function when the
   program writes one, or the structural impl's. *)
and trait_call cx (e : Tast.expr) (t : Hir.item) name self targs args =
  (* traits.coherence: a type constructor has at most one impl of a trait,
     so a method at a known [Self] is that impl's function. *)
  match norm self with
  | Con (owner, _)
    when declared_record owner
         && Model_fns.code cx (Impl (t, owner, name)) <> None ->
      code_call cx e (Impl (t, owner, name)) targs args
  | _ ->
      let values = List.map (fun (a : Tast.arg) -> expr cx a.value) args in
      Model_traits.structural_call cx e t name self values

(* A call of a function with code, at the instance its type arguments and its
   arguments' types give. *)
and code_call ?(maps = false) cx (e : Tast.expr) target targs args =
  let types = List.map (fun (a : Tast.arg) -> a.value.ty) args in
  let inst = Model_fns.instance cx target targs types in
  let f = tag "fnRef" [ Str inst.fkey; Arr []; Arr [] ] in
  let make passed = call_e cx f passed e.ty in
  if maps && Model_calls.has_map_inout args then
    let s = Model_fns.signature cx target in
    let _, raise = flat (Model_fns.instantiated_row inst s.row) in
    let cb =
      { Model_calls.expr = expr cx; place = place cx; store = assign cx None }
    in
    Model_calls.through_maps cb cx e ~raise make args
  else make (List.map (arg cx) args)

and writing cx : Model_writes.callbacks = { expr = expr cx; block = block cx }

and handlers cx : Model_handlers.callbacks =
  { expr = expr cx; block = block cx }

and shared cx : Model_shared.callbacks =
  { expr = expr cx; block = block cx; place = place cx }

and callbacks cx : Model_lists.callbacks =
  {
    expr = expr cx;
    stored = (fun target operands make -> stored cx target operands make);
  }

and call_value cx (f : Tast.expr) args result =
  call_e cx (expr cx f) (List.map (arg cx) args) result

and arg cx (a : Tast.arg) =
  match a.mode with
  | Inout -> tag "inout" [ place cx a.value ]
  | Let -> tag "value" [ expr cx a.value ]

and place cx (e : Tast.expr) =
  let extend b step =
    match place cx b with
    | Arr [ root; Arr steps ] -> Arr [ root; Arr (steps @ [ step ]) ]
    | p -> p
  in
  match e.desc with
  | Local v -> Arr [ Str (var_name v); Arr [] ]
  | Field (b, f) -> extend b (tag "field" [ Str f ])
  | Tuple_field (b, i) -> extend b (tag "field" [ Str (string_of_int i) ])
  | Index (b, _) when is_map b.ty -> outside "a place through a map's element"
  | Index (b, i) -> extend b (tag "index" [ expr cx i ])
  | _ -> outside "a place the model lacks"

and closure cx (e : Tast.expr) ps body =
  match norm e.ty with
  | Fn (sig_ps, result, r) ->
      (* expressions.closures: a parameter written as a pattern binds a fresh name, which
         the body matches against the pattern, irrefutable there
         (patterns.irrefutable-positions). *)
      let named i (p : Tast.pattern) =
        match p.pat with
        | P_bind v -> (var_name v, None)
        | _ -> (Printf.sprintf "%s/%d" (temp "closure-param" e.loc) i, Some p)
      in
      let names = List.mapi named ps in
      let param (n, _) (m, t) =
        Arr [ mode m; Str n; param_ty cx (m, t); Null ]
      in
      List.iter2
        (fun (p : Tast.pattern) (m, t) ->
          match p.pat with P_bind v -> writes cx m v t | _ -> ())
        ps sig_ps;
      let bound acc (n, p) =
        match p with
        | Some p -> tag "match" [ var_e n; ty cx result; Arr [ arm cx p acc ] ]
        | None -> acc
      in
      let saved = cx.yielding in
      cx.yielding <- None;
      let body =
        Fun.protect
          ~finally:(fun () -> cx.yielding <- saved)
          (fun () ->
            List.fold_left bound
              (raises_in cx r (fun () -> expr cx body))
              (List.rev names))
      in
      tag "closure"
        [ Arr (List.map2 param names sig_ps); ty cx result; row cx r; body ]
  | _ -> outside "a closure of a type the model lacks"

and eta_closure cx e make =
  let ps, body = eta e make in
  closure cx e ps body

and block cx (stmts : Tast.block) =
  match stmts with
  | [] -> unit_e
  | [ { stmt = Expr e; _ } ] -> expr cx e
  | { stmt; at } :: rest -> (
      match stmt with
      | Expr e -> tag "seq" [ expr cx e; block cx rest ]
      | Assign (_, { desc = Local w; _ }, _) when writable cx w ->
          outside "a view assigned to the whole of a writable binding"
      | Assign (o, p, v) when Model_projections.rooted p ->
          tag "seq"
            [ expr cx (Model_projections.assign cx at o p v); block cx rest ]
      | Let b -> binding cx "letIn" b rest
      | Var b -> binding cx "varIn" b rest
      | Assign (o, p, v) -> tag "seq" [ assign cx o p v; block cx rest ]
      | Assert c ->
          (* program.assert-expr: a panic of the kind [assert] when [c] is false. *)
          let fail = op (tag "panic" [ Str "assert" ]) [] in
          tag "seq"
            [
              tag "if" [ expr cx c; ty cx (Types.Tuple []); unit_e; fail ];
              block cx rest;
            ]
      | Yield p -> tag "seq" [ yield_ cx p; block cx rest ])

(* [yield p] in a projection written for an access: the access called with [p] and the
   places it threads, [inout], its value kept (projections.when-projection-runs). *)
and yield_ cx (p : Tast.expr) =
  match cx.yielding with
  | None -> outside "a yield"
  | Some a ->
      let args =
        List.map (fun value -> { Tast.mode = Inout; value }) (p :: a.extras)
      in
      let e =
        { Tast.desc = Call_value (a.k, args); ty = a.result; loc = p.loc }
      in
      let call =
        if Model_calls.has_map_inout args then
          let make passed = call_e cx (expr cx a.k) passed a.result in
          let cb =
            {
              Model_calls.expr = expr cx;
              place = place cx;
              store = assign cx None;
            }
          in
          let raise =
            match norm a.k.ty with Fn (_, _, r) -> snd (flat r) | _ -> None
          in
          Model_calls.through_maps cb cx e ~raise make args
        else expr cx e
      in
      tag "assign"
        [
          Arr [ Str a.res; Arr [] ]; tag "list" [ ty cx a.result; Arr [ call ] ];
        ]

(* What [return] gives: its operand's value, and in a projection written for an access,
   which returns no value, the access's value. *)
and returned cx = function
  | Some x -> expr cx x
  | None -> (
      match cx.yielding with
      | Some a -> tag "index" [ var_e a.res; tag "int" [ Str "0" ] ]
      | None -> unit_e)

and binding cx form (b : Tast.binding) rest =
  match (b.pattern.pat, b.otherwise) with
  | P_bind v, None
    when form = "varIn" && Model_views.viewed b.pattern.pty <> None ->
      Model_writes.binding (writing cx) cx v b.value rest
  | P_bind v, None ->
      tag form
        [
          Str (var_name v); ty cx b.pattern.pty; expr cx b.value; block cx rest;
        ]
  | P_wild, None -> tag "seq" [ expr cx b.value; block cx rest ]
  | _ ->
      (* A pattern binds as a match's arm does, and a let-else's [else] is the
         arm of every other value (patterns.let-else); a [var]'s binders are
         variables, each initialized with what the pattern binds. *)
      let body =
        if form = "letIn" then block cx rest
        else
          List.fold_right
            (fun (v, t) body ->
              let n = var_name v in
              tag "varIn" [ Str n; ty cx t; var_e n; body ])
            (typed_binders b.pattern) (block cx rest)
      in
      let others =
        match b.otherwise with
        | Some o -> [ Arr [ Str "wild"; Arr []; expr cx o ] ]
        | None -> []
      in
      tag "match"
        [
          expr cx b.value;
          ty cx (block_ty rest);
          Arr (arm cx b.pattern body :: others);
        ]

and assign cx o (p : Tast.expr) (v : Tast.expr) =
  match o with
  | None when not (through_map p) -> tag "assign" [ place cx p; expr cx v ]
  | None ->
      stored cx p [ v ] (fun _ vs -> match vs with [ x ] -> x | _ -> unit_e)
  | Some b ->
      stored cx p [ v ] (fun read vs ->
          match vs with [ value ] -> binary b p.ty v.ty read value | _ -> read)

(* Whether a place goes through a map's element (std.map-element-places). *)
and through_map (e : Tast.expr) =
  match e.desc with
  | Field (b, _) | Tuple_field (b, _) -> through_map b
  | Index (b, _) -> is_map b.ty || through_map b
  | _ -> false

(* A store into a place that also reads it, as [p op= e] and a call with an
   [inout self] receiver are: the place's index expressions are evaluated once,
   into temporaries, then the other operands, in order, then the place is read
   (values.compound-assignment-order and values.inout-argument-order). *)
and stored cx (target : Tast.expr) operands make =
  let lets, store, read = Model_places.receiver ~expr:(expr cx) cx target in
  let named =
    List.mapi
      (fun i (x : Tast.expr) ->
        (Printf.sprintf "operand/%d:%d/%d" x.loc.line x.loc.col i, x))
      operands
  in
  let lets =
    lets
    @ List.map (fun (n, (x : Tast.expr)) -> (n, ty cx x.ty, expr cx x)) named
  in
  let vars = List.map (fun (n, _) -> tag "var" [ Str n ]) named in
  let body = Model_places.write store (make read vars) in
  List.fold_right
    (fun (n, t, init) b -> tag "letIn" [ Str n; t; init; b ])
    lets body
