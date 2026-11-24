(* Expressions, blocks and statements (patterns.let-else). *)

open Hir
open Resolve_context
open Resolve_paths
open Resolve_types
open Resolve_patterns

(* The names of a path of identifiers, such as [fs.read] or [Self.new]. *)
let rec path_of (e : Ast.expr) =
  match e.desc with
  | Name name -> Some [ { desc = name; loc = e.loc } ]
  | Self_type -> Some [ { desc = "Self"; loc = e.loc } ]
  | Field (base, member) ->
      Option.map (fun path -> path @ [ member ]) (path_of base)
  | _ -> None

let item_expr item e =
  match e.kind with
  | Fn_item -> Func item
  | Const_item -> Const item
  | Variant_item -> Variant item
  | Type_item | Trait_item | Macro_item | Proc_item | Effect_item ->
      invalid_arg "Resolve.item_expr"

(* What a path's first names refer to, with the fields after them. In
   [Name.member], [Name] is a type when it can be (declarations.name-lookup). *)
let walked_path ctx path =
  match walk ctx ~want:Values ~noun:"a value" ~locals:true path with
  | Broken_ref, _, _ -> (Error, [])
  | Var_ref v, _, fields -> (Local v, fields)
  (* macros.uses: a macro is used with its [!]. *)
  | Item_ref (_, { kind = Macro_item; _ }), (last : name), _ ->
      errorf ctx Code.e0212 last.loc "`%s` is a macro, used as `%s!(…)`"
        last.desc last.desc;
      (Error, [])
  (* macros.meta-use: and a procedural macro only through [meta use]. *)
  | Item_ref (_, { kind = Proc_item; _ }), (last : name), _ ->
      errorf ctx Code.e0212 last.loc
        "`%s` is a procedural macro, used as `m.%s!(…)` where `meta use` names \
         its module `m`"
        last.desc last.desc;
      (Error, [])
  | Item_ref (item, ({ kind = Fn_item; _ } as e)), (last : name), fields ->
      (* macros.expansion-effects: the functions that a template names. *)
      Option.iter
        (fun named -> ctx.env.st.named <- Some ((item, last.loc) :: named))
        ctx.env.st.named;
      (item_expr item e, fields)
  | Item_ref (item, e), _, fields when not (is_type_kind e.kind) ->
      (item_expr item e, fields)
  | Item_ref (item, { kind = Trait_item; _ }), _, member :: fields ->
      (Member (Of_trait item, member), fields)
  (* handlers.performing-operation and handlers.advanced-tier: an operation of an effect, which a call
     performs. *)
  | Item_ref (item, { kind = Effect_item; _ }), _, member :: fields ->
      advanced ctx;
      (Perform (item, member), fields)
  | m, last, member :: fields when Option.is_some (as_type m last.loc) ->
      (Member (Of_type (Option.get (as_type m last.loc)), member), fields)
  | m, (last : name), _ ->
      errorf ctx Code.e0212 last.loc "`%s` is %s, not a value" last.desc
        (describe_meaning m);
      (Error, [])

(* The expression a path stands for: what its names refer to, then fields. A
   value parameter hides an item of its name, and no local takes it (generics.value-parameters-in-body). *)
let value_path ctx loc path =
  let at desc = { desc; loc } in
  let desc, fields =
    match path with
    | (first : name) :: fields
      when (not (List.mem_assoc first.desc ctx.locals))
           && List.mem_assoc first.desc ctx.value_params ->
        let v, t = List.assoc first.desc ctx.value_params in
        (Value_param (v, t), fields)
    | _ -> walked_path ctx path
  in
  List.fold_left (fun base field -> at (Field (base, field))) (at desc) fields

let self_value ctx loc =
  match List.assoc_opt "self" ctx.locals with
  | Some (Some v) -> Local v
  | Some None -> Error
  | None ->
      errorf ctx Code.e0215 loc "`self` exists only in methods";
      Error

let rec resolve_expr ctx (e : Ast.expr) : expr =
  let at desc = { desc; loc = e.loc } in
  match path_of e with
  | Some path -> value_path ctx e.loc path
  | None -> (
      match e.desc with
      | Name _ | Self_type -> invalid_arg "Resolve.resolve_expr"
      | Int s -> at (Int s)
      | Float s -> at (Float s)
      | Str s -> at (Str s)
      | Bool x -> at (Bool x)
      | Interpolated segments ->
          at (Interpolated (List.map (resolve_segment ctx) segments))
      | Self_value -> at (self_value ctx e.loc)
      | Field (base, member) -> at (Field (resolve_expr ctx base, member))
      | Key_root -> at Key_root
      | Hole -> at Hole
      | Tuple es -> at (Tuple (List.map (resolve_expr ctx) es))
      | List es -> at (List (List.map (resolve_expr ctx) es))
      | Call (f, args) ->
          at (Call (resolve_expr ctx f, List.map (resolve_arg ctx) args))
      | Index (base, index) ->
          at (Index (resolve_expr ctx base, resolve_expr ctx index))
      | Struct _ | Record_literal _ | Spread _ -> at (resolve_record ctx e)
      | Unary (op, operand) -> at (Unary (op, resolve_expr ctx operand))
      | Binary (op, a, b) ->
          let a = resolve_expr ctx a in
          at (Binary (op, a, resolve_expr ctx b))
      | Else (a, b) ->
          let a = resolve_expr ctx a in
          at (Else (a, resolve_expr ctx b))
      | Try (operand, arms) ->
          let operand = resolve_expr ctx operand in
          at (Try (operand, Option.map (List.map (resolve_arm ctx)) arms))
      | Raise operand -> at (Raise (resolve_expr ctx operand))
      | Return operand -> at (Return (Option.map (resolve_expr ctx) operand))
      | Break -> at (jump ctx e.loc "break" Break)
      | Continue -> at (jump ctx e.loc "continue" Continue)
      | Closure (params, body) -> at (resolve_closure ctx params body)
      | Block block -> at (Block (resolve_block ctx block))
      | If (cond, body, alt) -> at (resolve_if ctx cond body alt)
      | If_let (pattern, scrutinee, body, alt) ->
          at (resolve_if_let ctx pattern scrutinee body alt)
      | Match (scrutinee, arms) ->
          let scrutinee = resolve_expr ctx scrutinee in
          at (Match (scrutinee, List.map (resolve_arm ctx) arms))
      | Loop body -> at (Loop (resolve_block { ctx with in_loop = true } body))
      | While (cond, body) ->
          let cond = resolve_expr ctx cond in
          at (While (cond, resolve_block { ctx with in_loop = true } body))
      | For (pattern, iterable, body) ->
          at (resolve_for ctx pattern iterable body)
      | Macro_use (path, groups) -> resolve_macro ctx e.loc path groups
      | Handler _ | With _ | Resume _ | Comptime _ | Unsafe _ ->
          at (resolve_handling ctx e)
      | When (names, body) -> at (resolve_when ctx names body)
      | Bound_test (t, bounds) -> at (resolve_bound_test ctx t bounds)
      | Quote _ | Q_splice _ | Q_spread _ | Q_member _ | Q_record _ | Q_struct _
        ->
          resolve_quoting ctx e)

and resolve_if ctx cond body alt =
  let cond = resolve_expr ctx cond in
  let body = resolve_block ctx body in
  If (cond, body, Option.map (resolve_expr ctx) alt)

(* macros.quote and macros.splices: a quote, and the forms that splice into one. *)
and resolve_quoting ctx (e : Ast.expr) : expr =
  let at desc = { desc; loc = e.loc } in
  let fields base spliced =
    Option.iter (fun b -> ignore (resolve_expr ctx b)) base;
    List.iter (resolve_spliced_field ctx) spliced;
    at Error
  in
  match e.desc with
  | Quote q -> at (resolve_quote ctx q)
  | Q_splice _ -> Resolve_macros.splice ctx In_expr e (at Error)
  | Q_spread _ -> Resolve_macros.splice ctx In_elements e (at Error)
  | Q_member (base, s) ->
      ignore (resolve_expr ctx base);
      Resolve_macros.splice ctx In_name s (at Error)
  | Q_record (base, spliced) -> fields base spliced
  | Q_struct (path, base, spliced) ->
      ignore (record_ty ctx path);
      fields base spliced
  | _ -> invalid_arg "Resolve.resolve_quoting"

(* macros.quote-hygiene and macros.meta-tier: a quote, which makes its module meta. Its
   names resolve where it is written, among the bindings it makes and the
   items and imports of its module, never the locals of the code around it,
   and its splices are that code, resolved there. Its uses of macros expand
   in each expansion, not here. *)
and resolve_quote ctx (q : Ast.quote) =
  meta ctx;
  let st = ctx.env.st in
  let declaring = st.declaring in
  let splices = ref [] in
  let splice place (s : Ast.expr) =
    match s.desc with
    | (Q_splice e | Q_spread e)
      when not (List.exists (fun (x : splice) -> x.at = s.loc) !splices) ->
        let inside = st.declaring and quoted = st.named in
        st.declaring <- declaring;
        st.named <- None;
        let value = resolve_expr ctx e in
        st.declaring <- inside;
        st.named <- quoted;
        let spread = match s.desc with Q_spread _ -> true | _ -> false in
        splices := { place; spread; at = s.loc; value } :: !splices
    | _ -> ()
  in
  let quoting = { splice; outer = List.map fst ctx.locals } in
  let inner =
    {
      (module_ctx ctx.env ctx.scope) with
      in_loop = true;
      expanding = ctx.expanding;
      quoting = Some quoting;
    }
  in
  st.declaring <- true;
  (* macros.expansion-effects: the functions the contents name, which the
     quotes inside them add to. *)
  let named = st.named in
  st.named <- Some [];
  let form =
    Fun.protect
      ~finally:(fun () -> st.declaring <- declaring)
      (fun () -> resolve_quoted inner q.form)
  in
  let names = List.rev (Option.value st.named ~default:[]) in
  st.named <- Option.map (fun outer -> List.rev_append names outer) named;
  let by_place (a : splice) (b : splice) =
    compare (a.at.line, a.at.col) (b.at.line, b.at.col)
  in
  Quote
    {
      home = ctx.scope.name;
      form;
      tokens = q.tokens;
      splices = List.sort by_place !splices;
      names;
    }

(* The contents of a quote, resolved in the quote's own context. *)
and resolve_quoted inner : Ast.quote_form -> code = function
  | Quote_block b ->
      ignore (resolve_block inner b);
      Code_expr
  | Quote_type t ->
      ignore (resolve_ty inner t);
      Code_type
  | Quote_pattern p ->
      ignore (resolve_pattern inner (binder ()) p);
      Code_pattern
  | Quote_field f ->
      resolve_spliced_field inner f;
      Code_field

(* A field of a record literal in a quote (macros.splices). *)
and resolve_spliced_field ctx : Ast.spliced_field -> unit = function
  | Field_init f -> ignore (resolve_expr ctx f.value)
  | Spliced_field (s, v) ->
      Resolve_macros.splice ctx In_name s ();
      ignore (resolve_expr ctx v)
  | Spread_fields s -> Resolve_macros.splice ctx In_fields s ()

(* meta.bound-tests and meta.reflection-tier: a bound test names a type parameter in scope
   (E0212), with bounds as a generic writes them, and makes its module
   meta. *)
and resolve_bound_test ctx (t : name) bounds =
  meta ctx;
  let tested =
    match
      walk_to_end ctx ~want:Types ~noun:"a type parameter in scope" [ t ]
    with
    | Param_ref v, _ -> Some v
    | Broken_ref, _ -> None
    | m, last ->
        wrong_kind ctx last m "a type parameter in scope";
        None
  in
  let bounds =
    List.map (fun b -> (resolve_bound ctx ~implied_by:t.desc b).bound) bounds
  in
  match tested with Some v -> Bound_test (v, bounds) | None -> Error

(* shared.when and tasks.advanced-tier: [when] names local bindings or parameters, each
   once (E0433), and in its block each name is a binding of its own, the
   place of the value its handle reaches. Whether a name's type is
   [Shared<T>] is for type checking. *)
and resolve_when ctx names body =
  advanced ctx;
  let held = ref [] in
  let one inner (n : name) =
    let outer = value_path ctx n.loc [ n ] in
    (match outer.desc with
    | Local v when List.mem v.id !held ->
        errorf ctx Code.e0433 n.loc "`%s` is named twice in this `when`" n.desc
    | Local v -> held := v.id :: !held
    | Error -> ()
    | _ ->
        errorf ctx Code.e0433 n.loc
          "`%s` isn't a local binding or a parameter, so `when` can't hold it"
          n.desc);
    let v = fresh ctx n in
    ({ inner with locals = (n.desc, Some v) :: inner.locals }, (outer, v))
  in
  let inner, names = List.fold_left_map one ctx names in
  When (names, resolve_block inner body)

(* handlers.handler-literals, handlers.with and handlers.resuming: handler literals, [with] and [resume], and
   the Reference's staging annotations. *)
and resolve_handling ctx (e : Ast.expr) =
  match e.desc with
  | Handler (eff, answer, fns) ->
      Resolve_effects.resolve_handler ctx ~block:resolve_block e.loc eff answer
        fns
  | With (handlers, body) ->
      advanced ctx;
      let handlers = List.map (resolve_expr ctx) handlers in
      With (handlers, resolve_block ctx body)
  | Resume value -> Resume (Option.map (resolve_expr ctx) value)
  (* meta.staging-annotations and meta.staging-tier: a staging annotation, which makes its module
     meta. *)
  | Comptime form ->
      meta ctx;
      Comptime (resolve_expr ctx form)
  | Unsafe (reason, body) -> resolve_unsafe ctx reason body
  | _ -> invalid_arg "Resolve.resolve_handling"

(* c.unsafe-because and c.systems-tier: an [unsafe] block, whose reason holds a character
   that isn't whitespace (E0437), and which makes its module systems. *)
and resolve_unsafe ctx (reason : string Ast.node) body =
  systems ctx;
  let blank c = c = ' ' || c = '\t' || c = '\n' in
  if String.for_all blank reason.desc then
    errorf ctx Code.e0437 reason.loc
      "an `unsafe` block says why its code is sound, in a reason that isn't \
       empty";
  Unsafe (resolve_block ctx body)

(* macros.uses and macros.expansion: an expression macro's use, expanded in its place. *)
and resolve_macro ctx loc path groups =
  match
    Resolve_macros.expand ctx loc path groups Macro_expand.Expr
      (fun ctx tokens ->
        Macro_expand.parse_expr ~file:ctx.scope.file ~at:loc tokens)
      resolve_expr
  with
  | Some e -> e
  | None -> { desc = Error; loc }

(* Struct literals, anonymous records and their updates (records.anonymous-literals and records.update
   and 8), and spreads (variadics.spread-expressions). *)
and resolve_record ctx (e : Ast.expr) =
  match e.desc with
  | Struct (path, base, fields) ->
      let ty = record_ty ctx path in
      let base = Option.map (resolve_expr ctx) base in
      Struct (ty, base, List.map (resolve_field_init ctx) fields)
  | Record_literal (base, fields) ->
      advanced ctx;
      let base = Option.map (resolve_expr ctx) base in
      Record_literal (base, List.map (resolve_field_init ctx) fields)
  | Spread e -> Spread (resolve_expr ctx e)
  | _ -> invalid_arg "Resolve.resolve_record"

and resolve_segment ctx : Ast.segment -> segment = function
  | Text s -> Text s
  | Splice (e, spec) -> Splice (resolve_expr ctx e, spec)

and resolve_arg ctx ({ inout; value } : Ast.arg) =
  { inout; value = resolve_expr ctx value }

(* A field is no name of a scope, though a template writes it (macros.hygiene). *)
and resolve_field_init ctx ({ field; value } : Ast.field_init) =
  let field = { field with desc = Macro_marks.base field.desc } in
  { field; value = resolve_expr ctx value }

and resolve_closure ctx params body =
  let b = binder () in
  let param ({ mode; pattern; annotation } : Ast.closure_param) =
    let annotation = Option.map (resolve_ty ctx) annotation in
    { mode; pattern = resolve_pattern ctx b pattern; annotation }
  in
  let params = List.map param params in
  let inner = { (with_bound ctx b) with in_loop = false } in
  Closure (params, resolve_expr inner body)

(* The pattern's variables are in scope in the first block only (expressions.scope). *)
and resolve_if_let ctx pattern scrutinee body alt =
  let scrutinee = resolve_expr ctx scrutinee in
  let b = binder () in
  let pattern = resolve_pattern ctx b pattern in
  let body = resolve_block (with_bound ctx b) body in
  If_let (pattern, scrutinee, body, Option.map (resolve_expr ctx) alt)

and resolve_for ctx pattern iterable body =
  let iterable =
    match iterable with
    | Iter e -> Iter (resolve_expr ctx e)
    | Range (a, b, kind) ->
        let a = resolve_expr ctx a in
        Range (a, resolve_expr ctx b, kind)
  in
  let b = binder () in
  let pattern = resolve_pattern ctx b pattern in
  let inner = { (with_bound ctx b) with in_loop = true } in
  For (pattern, iterable, resolve_block inner body)

(* expressions.break-and-continue *)
and jump ctx loc keyword desc =
  if ctx.in_loop then desc
  else (
    errorf ctx Code.e0216 loc "`%s` is outside the body of every loop" keyword;
    Error)

and resolve_arm ctx ({ pattern; guard; because; body } : Ast.arm) : arm =
  let b = binder () in
  let pattern = resolve_pattern ctx b pattern in
  let ctx = with_bound ctx b in
  let guard = Option.map (resolve_expr ctx) guard in
  { pattern; guard; because; body = resolve_expr ctx body }

and resolve_block ctx = function
  | [] -> []
  | (s : Ast.stmt) :: rest ->
      let after, desc = resolve_stmt ctx s in
      { desc; loc = s.loc } :: resolve_block after rest

and resolve_stmt ctx (s : Ast.stmt) =
  match s.desc with
  | Let binding ->
      let ctx, binding = resolve_binding ctx binding in
      (ctx, Let binding)
  | Var binding ->
      let ctx, binding = resolve_binding ctx binding in
      (ctx, Var binding)
  | Assign (op, place, value) ->
      let place = resolve_expr ctx place in
      (ctx, Assign (op, place, resolve_expr ctx value))
  | Assert e -> (ctx, Assert (resolve_expr ctx e))
  | Yield e -> (ctx, Yield (resolve_expr ctx e))
  | Expr e -> (ctx, Expr (resolve_expr ctx e))

(* The pattern's variables are in scope after the statement, not in its
   value (expressions.scope). *)
and resolve_binding ctx ({ pattern; annotation; value } : Ast.binding) =
  let value = resolve_expr ctx value in
  let annotation = Option.map (resolve_ty ctx) annotation in
  let b = binder () in
  let pattern = resolve_pattern ctx b pattern in
  (with_bound ctx b, { pattern; annotation; value })
