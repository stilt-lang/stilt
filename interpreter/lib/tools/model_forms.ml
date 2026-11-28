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

(* A constructor's variant type, the type arguments it is written with, and its
   name. *)
let ctor_args cx (c : Hir.item) t =
  match Env.variant cx.env c with
  | Some (i, _, _) ->
      let name, args = declared_args cx i (args_of t) in
      (name, with_args args, c.name)
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
  let name, args = declared_args cx option_item (args_of t) in
  tag "variant" ((Str name :: with_args args) @ [ Str ctor; Arr payload ])

(* A name of a temporary of the export's, unique to the source position. *)
let temp what (loc : Ast.loc) = Printf.sprintf "%s/%d:%d" what loc.line loc.col

(* Whether the prelude's structural impls of the trait [name] give a type's,
   whose parts are integers, floats, [bool], [str], lists, tuples, maps and sets
   for [Eq] and [Show], and the program's records and variants without an impl of
   the trait of their own (std.show-output and traits.structural-impls). A map has
   [Eq] when its keys are key types and its values have [Eq], and a set when its
   elements are key types; the calculus compares them in any order
   (traits.map-equality and std.set-impls). Neither has [Ord]. *)
let structural_by cx name t =
  let trait = { Hir.home = "std.prelude"; name } in
  let rec go seen t =
    match norm t with
    | Types.Con ({ home = "std.prelude"; name }, [])
      when List.mem name Types.integer_types
           || List.mem name [ "f32"; "f64"; "bool"; "str" ] ->
        true
    | Con ({ home = "std.prelude"; name = "List" }, [ e ]) -> go seen e
    (* generics.array-traits: an array has the structural impls when its elements do. *)
    | Con (i, [ e; _ ]) when i = array_item -> go seen e
    | Con ({ home = "std.prelude"; name = "Map" }, [ k; v ]) ->
        (name = "Show" && key cx k && go seen k && go seen v)
        || (name = "Eq" && key cx k && go seen v)
    | Con ({ home = "std.prelude"; name = "Set" }, [ e ]) ->
        (name = "Show" && go seen e) || (name = "Eq" && key cx e)
    | Tuple ts -> List.for_all (go seen) ts
    (* records.no-home: an anonymous record has the structural impls and no others. *)
    | Record fields -> List.for_all (fun (_, t) -> go seen t) fields
    | Con (i, args) -> (
        let sub t =
          instantiated cx { key = ""; item = i; args; generic = false } t
        in
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

(* [==] and the ordering operators on a type other than the numeric types,
   [bool] and [str], through the prelude's structural impls (traits.operators). *)
let structural_cmp cx b t =
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

(* The constructors of each variant type that a type holds, in declaration
   order, by the names the calculus declares them under (traits.structural-calls). *)
let ctor_orders cx t =
  let rec go (seen, acc) t =
    match norm t with
    | Types.Con ({ home = "std.prelude"; name = "List" }, [ e ]) ->
        go (seen, acc) e
    | Types.Con (i, [ e; _ ]) when i = array_item -> go (seen, acc) e
    | Tuple ts -> List.fold_left go (seen, acc) ts
    | Con (i, args) when not (List.mem (i, args) seen) -> (
        let seen = (i, args) :: seen in
        let parts acc ts =
          List.fold_left go acc
            (List.map
               (instantiated cx { key = ""; item = i; args; generic = false })
               ts)
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

(* traits.trait-constants: a trait constant's read at the type [self], as the expression of
   its value: the impl's for [self]'s head, at [self]'s arguments, or the trait's default,
   with [self] as its [Self] and the impl's arguments as the trait's parameters. Its value
   is a constant expression, pure, so reading it where it is read gives the value a first
   evaluation would (declarations.constant-evaluation). *)
let trait_constant cx (_ : Tast.expr) trait name self : Tast.expr =
  let code = function
    | Some (Tast.Code x) -> x
    | _ -> outside "a constant without code"
  in
  let at tenv x =
    Check_zonk.map_expr ~ty:(Types.subst tenv []) ~row:(Types.subst_row tenv [])
      x
  in
  let impl =
    match norm self with
    | Con (owner, args) -> (
        match Env.trait_impl cx.env ~trait owner with
        | Some impl
          when List.exists (fun (m : Env.member) -> m.name = name) impl.members
          ->
            Some (owner, Env.impl_subst cx.env [] impl args)
        | _ -> None)
    | _ -> None
  in
  match (impl, Env.trait_info cx.env trait) with
  | Some (owner, tenv), _ ->
      at tenv
        (code (List.assoc_opt (trait, owner, name) cx.program.impl_constants))
  | None, Some info ->
      let targs =
        Option.value ~default:[] (Env.trait_args cx.env [] self trait)
      in
      if List.length targs <> List.length info.params then
        outside "the default of a trait with parameters";
      let tenv = (info.self_param, self) :: List.combine info.params targs in
      at tenv (code (List.assoc_opt (trait, name) cx.program.default_constants))
  | None, None -> outside "a constant"

(* The name a constant is declared with in the model: its item's, or its owner's and
   its own. *)
let const_name (e : Tast.expr) =
  match e.desc with
  | Constant i -> i.home ^ "." ^ i.name
  | Member_constant (owner, m, _) -> owner.home ^ "." ^ owner.name ^ "." ^ m
  | _ -> outside "a constant"

(* patterns.constants: the literal pattern that matches the values equal to a constant's
   value [e], when its value is a literal of a type the model's patterns write: an
   integer, possibly negated (numbers.negative-literals), a Boolean, a string, [()] or a
   tuple of those. *)
let rec literal_pattern (e : Tast.expr) =
  let int t text ~negated =
    match int_kind t with
    | Some kind ->
        let v = literal_value kind text in
        let v =
          if (not negated) || String.starts_with ~prefix:"-" v || v = "0" then v
          else "-" ^ v
        in
        Some (tag "int" [ Str v ])
    | None -> None
  in
  match e.desc with
  | Int text -> int e.ty text ~negated:false
  | Unary (Neg, { desc = Int text; ty; _ }) -> int ty text ~negated:true
  | Bool b -> Some (tag "bool" [ Bool b ])
  | Str s -> Some (tag "str" [ Str s ])
  | Tuple [] -> Some (Str "unit")
  | Tuple es ->
      let ps = List.filter_map literal_pattern es in
      if List.length ps = List.length es then Some (tag "tuple" [ Arr ps ])
      else None
  | _ -> None

let const_literal cx c = literal_pattern (constant cx c)

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
      let list = tag "list" [ Arr (List.map (pattern cx) ps); rest ] in
      if is_array p.pty then
        tag "record"
          [ Str (record_name cx p.pty); Arr [ Arr [ Str array_field; list ] ] ]
      else list
  | P_or (q :: qs) ->
      List.fold_left
        (fun acc q -> tag "or" [ acc; pattern cx q ])
        (pattern cx q) qs
  | P_const c -> (
      (* The constant, declared in the model with its value, and the literal pattern of
         its value (patterns.constants). *)
      match const_literal cx c with
      | Some v ->
          let name = const_name c in
          if not (List.mem_assoc name cx.consts) then
            cx.consts <- (name, constant cx c) :: cx.consts;
          tag "const" [ Str name; v ]
      | None -> outside "a constant pattern whose value is no literal")
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

let guarded_arm cx p guard body =
  Arr [ pattern cx p; Arr (binders p); Option.value guard ~default:Null; body ]

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
