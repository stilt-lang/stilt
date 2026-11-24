(* The parts of the export of expressions that no expression's translation
   needs in turn: the operations on the world, the prelude's types, temporaries, patterns and whether a type's [Show] is
   structural. *)

open Model_json
open Model_types
open Model_ops

let unit_e = Str "unit"

let ctor cx (c : Hir.item) t =
  match Env.variant cx.env c with
  | Some (i, _, _) -> (declared cx i (args_of t), c.name)
  | None -> outside "the constructor %s" (item_name c)

let map_item = { Hir.home = "std.prelude"; name = "Map" }

let is_map t =
  match norm t with Types.Con (i, [ _; _ ]) -> i = map_item | _ -> false

let map_op name operands = op (tag "map" [ Str name ]) operands
let list_item = { Hir.home = "std.prelude"; name = "List" }
let option_item = { Hir.home = "std.prelude"; name = "Option" }
let prelude_ty name = Types.Con ({ home = "std.prelude"; name }, [])
let var_e n = tag "var" [ Str n ]

let fn_result t =
  match norm t with
  | Types.Fn (_, r, _) -> r
  | _ -> outside "a call of a value that isn't a function"

let call_e cx f args result = tag "call" [ f; Arr args; ty cx result ]

let is_never t =
  match norm t with
  | Types.Con ({ home = "std.prelude"; name = "Never" }, []) -> true
  | _ -> false

(* The traits whose written impls operators and splices call. *)
let prelude_trait name = { Hir.home = "std.prelude"; name }
let eq_trait = prelude_trait "Eq"
let ord_trait = prelude_trait "Ord"
let show_trait = prelude_trait "Show"
let ordering_item = prelude_trait "Ordering"

(* [T], for the type [Option<T>], and the type itself for any other. *)
let option_payload t =
  match norm t with Types.Con (i, [ p ]) when i = option_item -> p | t -> t

(* A value of [Option<T>], for the type [t] of [Option<T>]. *)
let option cx t ctor payload =
  tag "variant"
    [ Str (declared cx option_item (args_of t)); Str ctor; Arr payload ]

(* A name of a temporary of the export's, unique to the source position. *)
let temp what (loc : Ast.loc) = Printf.sprintf "%s/%d:%d" what loc.line loc.col

(* Whether the prelude's structural impls of the trait [name] give a type's,
   whose parts are integers, floats, [bool], [str], lists, tuples, maps for
   [Show] only, and the program's records and variants without an impl of the
   trait of their own (std.show-output and traits.structural-impls). Map
   equality ignores the order of the entries (traits.map-equality), which the
   calculus's comparison doesn't. *)
let structural_by cx name t =
  let trait = { Hir.home = "std.prelude"; name } in
  let rec go seen t =
    match norm t with
    | Types.Con ({ home = "std.prelude"; name }, [])
      when List.mem name Types.integer_types
           || List.mem name [ "f32"; "f64"; "bool"; "str" ] ->
        true
    | Con ({ home = "std.prelude"; name = "List" }, [ e ]) -> go seen e
    | Con ({ home = "std.prelude"; name = "Map" }, [ k; v ]) ->
        name = "Show" && go seen k && go seen v
    | Con ({ home = "std.prelude"; name = "Set" }, [ e ]) ->
        name = "Show" && go seen e
    | Tuple ts -> List.for_all (go seen) ts
    (* records.no-home: an anonymous record has the structural impls and no others. *)
    | Record fields -> List.for_all (fun (_, t) -> go seen t) fields
    | Con (i, args) -> (
        let sub t = instantiated cx { key = ""; item = i; args } t in
        let parts ts = List.for_all (fun t -> go (i :: seen) (sub t)) ts in
        List.mem i seen
        || Env.trait_impl cx.env ~trait i = None
           &&
           match Env.type_info cx.env i with
           | Some { Env.def = Env.Record fields; _ } when declared_record i ->
               parts (List.map snd fields)
           | Some { Env.def = Env.Variants ctors; _ } ->
               List.for_all (fun (_, ts) -> parts ts) ctors
           | _ -> false)
    | _ -> false
  in
  go [] t

let structural cx t = structural_by cx "Show" t

(* The constructors of each variant type that a type holds, in declaration
   order, by the names the calculus declares them under (traits.structural-calls). *)
let ctor_orders cx t =
  let rec go (seen, acc) t =
    match norm t with
    | Types.Con ({ home = "std.prelude"; name = "List" }, [ e ]) ->
        go (seen, acc) e
    | Tuple ts -> List.fold_left go (seen, acc) ts
    | Con (i, args) when not (List.mem (i, args) seen) -> (
        let seen = (i, args) :: seen in
        let parts acc ts =
          List.fold_left go acc
            (List.map (instantiated cx { key = ""; item = i; args }) ts)
        in
        match Env.type_info cx.env i with
        | Some { Env.def = Env.Variants ctors; _ } ->
            let acc = (declared cx i args, List.map fst ctors) :: acc in
            parts (seen, acc) (List.concat_map snd ctors)
        | Some { Env.def = Env.Record fields; _ } when declared_record i ->
            parts (seen, acc) (List.map snd fields)
        | _ -> (seen, acc))
    | _ -> (seen, acc)
  in
  List.rev (snd (go ([], []) t))

(* An operation on the world: a write to the output or to standard error, or a read of
   the input (std.io). *)
let on_world name fields operands =
  op (tag "world" (Str name :: fields)) operands

(* [print(s)], [eprint(s)], [io.write(s)] and [io.ewrite(s)]: [s] appended to the output,
   or to standard error with [~err], then a newline with [~newline] (std.io). *)
let written ~err ~newline s = on_world "write" [ Bool err; Bool newline ] [ s ]

let option_pattern cx t payload =
  tag "variant"
    [ Str (declared cx option_item (args_of t)); Str "Some"; Arr payload ]

let rec pattern cx (p : Tast.pattern) =
  match p.pat with
  | P_wild -> Str "wild"
  | P_bind v -> tag "bind" [ Str (var_name v) ]
  | P_int text -> (
      match int_kind p.pty with
      | Some k -> tag "int" [ Str (literal_value k text) ]
      | None -> outside "a literal pattern of a type the model lacks")
  | P_str s -> tag "str" [ Str s ]
  | P_bool b -> tag "bool" [ Bool b ]
  | P_tuple [] -> Str "unit"
  | P_tuple ps -> tag "tuple" [ Arr (List.map (pattern cx) ps) ]
  | P_variant (c, ps) ->
      let t, name = ctor cx c p.pty in
      tag "variant" [ Str t; Str name; Arr (List.map (pattern cx) ps) ]
  | P_record fields -> (
      match norm p.pty with
      | Con (i, _) when declared_record i ->
          let field (f, q) = Arr [ Str f; pattern cx q ] in
          tag "record"
            [ Str (record_name cx p.pty); Arr (List.map field fields) ]
      | Record _ ->
          let field (f, q) = Arr [ Str f; pattern cx q ] in
          tag "record"
            [ Str (record_name cx p.pty); Arr (List.map field fields) ]
      | _ -> outside "a record pattern of a type the model lacks")
  | P_list (ps, rest) ->
      let rest =
        match rest with
        | Exact -> Str "exact"
        | Rest -> Str "any"
        | Rest_bind v -> tag "bind" [ Str (var_name v) ]
      in
      tag "list" [ Arr (List.map (pattern cx) ps); rest ]
  | P_or (q :: qs) ->
      List.fold_left
        (fun acc q -> tag "or" [ acc; pattern cx q ])
        (pattern cx q) qs
  | _ -> outside "a pattern the model lacks"

let rec binders (p : Tast.pattern) =
  match p.pat with
  | P_bind v -> [ Str (var_name v) ]
  | P_tuple ps | P_variant (_, ps) -> List.concat_map binders ps
  | P_record fields -> List.concat_map (fun (_, q) -> binders q) fields
  | P_or (q :: _) -> binders q
  | P_list (ps, rest) -> (
      List.concat_map binders ps
      @
      match rest with
      | Rest_bind v -> [ Str (var_name v) ]
      | Exact | Rest -> [])
  | _ -> []

let rec typed_binders (p : Tast.pattern) =
  match p.pat with
  | P_bind v -> [ (v, p.pty) ]
  | P_tuple ps | P_variant (_, ps) -> List.concat_map typed_binders ps
  | P_record fields -> List.concat_map (fun (_, q) -> typed_binders q) fields
  | P_or (q :: _) -> typed_binders q
  | P_list (ps, rest) -> (
      (* patterns.pattern-forms: [..rest] binds the rest as a list of the
         elements' type. *)
      List.concat_map typed_binders ps
      @
      match rest with
      | Rest_bind v -> [ (v, Types.Con (list_item, [ elem p.pty ])) ]
      | Exact | Rest -> [])
  | _ -> []

(* A block's type: its last expression's, or [()]. *)
let block_ty (stmts : Tast.block) =
  match List.rev stmts with
  | { stmt = Expr e; _ } :: _ -> e.ty
  | _ -> Types.Tuple []

let arm cx p body = Arr [ pattern cx p; Arr (binders p); body ]

(* A function or a constructor as a value [e] of type [fn(...) -> R / r], as the closure
   that calls it with its parameters, [|a, b| f(a, b)], which a run can't tell from it:
   a function value has no identity of its own (types.function-types). [make] gives the
   call of the arguments, at the row [r]. *)
let eta (e : Tast.expr) make =
  match norm e.ty with
  | Fn (ps, result, r) ->
      let var i : Hir.var =
        { id = -1 - i; name = temp "eta" e.loc; loc = e.loc }
      in
      let vars = List.mapi (fun i _ -> var i) ps in
      let pattern v (_, t) : Tast.pattern =
        { pat = P_bind v; pty = t; ploc = e.loc }
      in
      let arg v (m, t) : Tast.arg =
        { mode = m; value = { desc = Local v; ty = t; loc = e.loc } }
      in
      let call = make (List.map2 arg vars ps) r in
      ( List.map2 pattern vars ps,
        ({ desc = call; ty = result; loc = e.loc } : Tast.expr) )
  | _ -> outside "a function value of a type the model lacks"

(* A constant's read, as the expression its value is: the constant expression it is
   declared with (declarations.constant-expressions), an integer type's [MIN] or [MAX] as
   the literal of its value, and [NAN] and [INFINITY] as the quotients IEEE 754 gives, a
   quiet NaN and positive infinity (std.floats and numbers.ieee-754); every NaN orders
   alike (traits.floats). *)
let constant cx (e : Tast.expr) : Tast.expr =
  let code = function
    | Some (Tast.Code x) -> x
    | _ -> outside "a constant without code"
  in
  match e.desc with
  | Constant i -> code (List.assoc_opt i cx.program.constants)
  | Member_constant
      ({ home = "std.prelude"; name = k }, (("MIN" | "MAX") as m), _)
    when Ints.of_name k <> None ->
      let kind = Option.get (Ints.of_name k) in
      let v = if m = "MIN" then Ints.min_value kind else Ints.max_value kind in
      { e with desc = Int (Ints.to_string kind v) }
  | Member_constant
      ( { home = "std.prelude"; name = "f32" | "f64" },
        (("NAN" | "INFINITY") as m),
        _ ) ->
      let lit x = { e with desc = Float x } in
      let top = if m = "NAN" then "0.0" else "1.0" in
      { e with desc = Binary (Div, lit top, lit "0.0") }
  | Member_constant (owner, m, _) ->
      code (List.assoc_opt (owner, m) cx.program.member_constants)
  | _ -> outside "a constant"
