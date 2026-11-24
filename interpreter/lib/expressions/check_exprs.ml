(* Expressions. [infer] checks each form, here or in the module of its kind,
   and the modules that come before this one check the parts of a form
   through it, as every context holds it. *)

module T = Types
module A = Tast
open Check_state
open Check_expect
open Check_effects
open Check_types
open Check_fields
open Check_members
open Check_operators
open Check_closures
open Check_blocks
open Check_control
open Check_calls

(* variadics.spread-expressions: inside a spread, a pack tuple stands for its element. *)
let local_value st loc (v : Hir.var) =
  match Hashtbl.find_opt st.locals v.id with
  | Some ty -> (
      Check_spreads.names_local st ty;
      match
        Option.bind (Packs.pack_tuple ty) (fun (pack, element) ->
            Check_spreads.named_in_spread st loc v pack element)
      with
      | Some e -> e
      | None -> node (Local v) ty loc)
  | None -> node (Local v) T.Error loc

let function_value st loc item =
  match Env.function_sig st.env item with
  | Some { projection = true; _ } -> projection_value st loc
  | Some s ->
      let targs, params, ret, row =
        instantiate st loc s ~self:None ~use_at:loc
      in
      Check_foreign.used st loc (Function item) targs;
      node (Callee (Function item, targs)) (T.Fn (params, ret, row)) loc
  | None -> error_node loc

let constant_value st loc item =
  match Env.constant_type st.env item with
  | Some ty ->
      st.constants <- Global item :: st.constants;
      node (Constant item) ty loc
  | None -> error_node loc

(* A variant as a value: itself if it has no payload, or else its
   constructor. *)
let variant_value st loc item =
  match Env.variant st.env item with
  | Some (owner, _, payload) ->
      let ty, args, info = instantiate_type st loc owner in
      let payload =
        List.map (T.subst (List.combine info.params args) []) payload
      in
      if payload = [] then node (Construct (item, args, [])) ty loc
      else
        node
          (Constructor (item, args))
          (T.Fn (List.map (fun t -> (by_value, t)) payload, ty, T.empty_row))
          loc
  | None -> error_node loc

(* Whether a literal is expected to have the error type, which it then has,
   unchecked against the ranges of number types (macros.errors-in-expansions; errors.error-type). *)
let unchecked expected =
  match expected with Some t -> T.resolve t = T.Error | None -> false

(* A number literal's type, as [expected] has it. *)
let number_type st expected ~text ~negative ~float loc =
  if unchecked expected then T.Error else literal st ~text ~negative ~float loc

(* A literal [lit], with the [-] before it. *)
let negative_literal st expected loc (lit : Hir.expr) text =
  let float = match lit.desc with Float _ -> true | _ -> false in
  let ty = number_type st expected ~text ~negative:true ~float loc in
  let inner = node (if float then A.Float text else A.Int text) ty lit.loc in
  node (Unary (Neg, inner)) ty loc

let rec infer ctx expected (e : Hir.expr) : A.expr =
  let st = ctx.st in
  let at desc ty = node desc ty e.loc in
  match e.desc with
  | Int _ | Float _ | Str _ | Bool _ | Interpolated _ ->
      literal_expr ctx expected e
  | Local v -> instantiated st expected (local_value st e.loc v)
  (* generics.value-parameters-in-body: an immutable value of its type. *)
  | Value_param (v, t) -> at (Value_param v) (Env.of_hir t)
  | Func item -> function_value st e.loc item
  | Const item -> constant_value st e.loc item
  | Variant item -> variant_value st e.loc item
  | Member (owner, name) -> member_value ctx e.loc owner name
  | Key_root -> key_path_closure ctx expected e
  | (Field _ | Call _ | Index _) when key_path e ->
      key_path_closure ctx expected e
  | Hole -> at Hole (match expected with Some t -> t | None -> fresh st e.loc)
  | Tuple es -> tuple_expr ctx expected e.loc es
  | List es -> list_expr ctx expected e.loc es
  | Field (b, f) -> instantiated st expected (field_access ctx e.loc b f)
  (* handlers.performing-operation, handlers.handler-literals and handlers.resuming *)
  | Call (({ desc = Perform (eff, name); _ } as callee), args) ->
      Check_handlers.perform_op ctx e.loc callee eff name args
  | Perform (eff, name) -> Check_handlers.operation_value ctx e.loc eff name
  | Handler h -> Check_handlers.handler_lit ctx expected e.loc h
  | With (handlers, block) ->
      Check_with.with_expr ctx expected e.loc handlers block
  | Resume value -> Check_handlers.resume_expr ctx e.loc value
  | When (names, block) -> Check_when.when_expr ctx expected e.loc names block
  | Call (callee, args) -> call ctx e.loc callee args
  | Index (base, index) -> index_expr ctx e.loc base index
  | Struct _ | Record_literal _ | Spread _ -> record ctx expected e
  | Unary (op, operand) -> unary ctx expected e.loc op operand
  | Binary (op, a, b) -> binary ctx e.loc op a b
  | Else (a, b) -> else_expr ctx e.loc a b
  | Try (operand, arms) -> try_expr ctx expected e.loc operand arms
  | Raise value -> raise_expr ctx e.loc value
  | Return value -> return_expr ctx e.loc value
  | Break -> at Break T.never
  | Continue -> at Continue T.never
  | Closure (params, body) -> closure ctx expected e.loc params body
  | Block block -> block_value ctx expected e.loc block
  | If (cond, body, alt) -> if_expr ctx expected e.loc cond body alt
  | If_let (p, scrutinee, body, alt) ->
      if_let_expr ctx expected e.loc p scrutinee body alt
  | Match (scrutinee, arms) -> match_expr ctx expected e.loc scrutinee arms
  | Loop body -> loop_expr ctx e.loc body
  | While (cond, body) -> while_expr ctx e.loc cond body
  | For (target, iterable, body) -> for_expr ctx e.loc target iterable body
  | Unsafe block -> unsafe_block ctx expected e.loc block
  | Comptime form -> comptime ctx expected e.loc form
  (* meta.bound-tests: a bound test, which only an [if] holds. *)
  | Bound_test (v, bounds) ->
      at (Reflect (Implements (T.Param v, Check_meta.tested v bounds))) T.bool
  | Quote q -> Check_quotes.quote ctx e.loc q
  | Error ->
      st.broken <- true;
      Check_spreads.names_local st T.Error;
      error_node e.loc

(* c.unsafe-because: a block, whose operations may be unsafe. *)
and unsafe_block ctx expected loc block =
  Check_foreign.within ctx.st loc (fun () -> block_value ctx expected loc block)

(* meta.staging-annotations: the form, with its type. *)
and comptime ctx expected loc form =
  let form = infer ctx expected form in
  node (Comptime form) form.ty loc

and block_value ctx expected loc block =
  let b, ty = block_expr ctx ~at:loc expected block in
  node (Block b) ty loc

and literal_expr ctx expected (e : Hir.expr) =
  let st = ctx.st in
  let at desc ty = node desc ty e.loc in
  let number = number_type st expected ~negative:false e.loc in
  match e.desc with
  | Int text -> at (Int text) (number ~text ~float:false)
  | Float text -> at (Float text) (number ~text ~float:true)
  | Str s -> at (Str s) T.str
  | Bool b -> at (Bool b) T.bool
  | Interpolated segments ->
      at (Interpolated (List.map (segment ctx) segments)) T.str
  | _ -> invalid_arg "Check_exprs.literal_expr"

and unary ctx expected loc op (operand : Hir.expr) =
  match (op, operand.desc) with
  (* numbers.negative-literals: a [-] directly before a literal is part of it. *)
  | Neg, (Int text | Float text)
    when operand.loc.line = loc.line && operand.loc.col = loc.col + 1 ->
      negative_literal ctx.st expected loc operand text
  | Neg, _ ->
      let v = infer ctx expected operand in
      node (Unary (Neg, v)) (operator ctx.st v.ty Negatable loc) loc
  | Not, _ ->
      let v = infer ctx expected operand in
      node (Unary (Not, v)) (operator ctx.st v.ty Bool_or_integer loc) loc

(* Records, their updates (records.anonymous-literals and records.update), and spreads, which are
   elements or arguments, where the tuple, the list or the call checks them
   (variadics.spread-expressions). *)
and record ctx expected (e : Hir.expr) =
  match e.desc with
  | Struct (hty, None, fields) -> struct_literal ctx e.loc hty fields
  | Struct (hty, Some base, fields) ->
      Check_records.named_update ctx e.loc hty base fields
  | Record_literal (None, fields) ->
      Check_records.anonymous_literal ctx expected e.loc fields
  | Record_literal (Some base, fields) ->
      Check_records.anonymous_update ctx e.loc base fields
  | Spread inner -> Check_spreads.spread ctx e.loc inner
  | _ -> invalid_arg "Check_exprs.record"

and segment ctx (s : Hir.segment) : A.segment =
  let st = ctx.st in
  match s with
  | Text s -> Text s
  | Splice (e, spec) ->
      let v = infer ctx None e in
      obligation st v.ty (prelude_trait "Show") e.loc;
      Option.iter (fun spec -> st.specs <- (v.ty, spec, e.loc) :: st.specs) spec;
      Splice (v, spec)

and tuple_expr ctx expected loc es =
  if List.exists Check_spreads.is_spread es then
    Check_spreads.spread_tuple ctx loc es
  else plain_tuple ctx expected loc es

and plain_tuple ctx expected loc es =
  (* An element checked against a type has that type, so a [Never]
     element converts (declarations.never). *)
  let expected_items =
    match Option.map T.resolve expected with
    | Some (Tuple ts)
      when List.length ts = List.length es
           && not (List.exists Packs.is_spread ts) ->
        List.map Option.some ts
    | Some Error -> List.map (fun _ -> Some T.Error) es
    | _ -> List.map (fun _ -> None) es
  in
  let items = List.map2 (fun e x -> infer_checked ctx x e) es expected_items in
  let types =
    List.map2
      (fun (i : A.expr) x -> Option.value x ~default:i.ty)
      items expected_items
  in
  node (Tuple items) (T.Tuple types) loc

(* generics.array-literals: a list literal is an array where one is expected, and a
   [List] everywhere else. *)
and list_expr ctx expected loc es =
  match Option.bind expected Check_arrays.parts with
  | Some (elem, size) -> Check_arrays.literal ctx loc elem size es
  | None ->
      if List.exists Check_spreads.is_spread es then
        Check_spreads.spread_list ctx expected loc es
      else plain_list ctx expected loc es

and plain_list ctx expected loc es =
  let st = ctx.st in
  (* Without an expected element type, the first element establishes one,
     with room for the rows of the later ones. *)
  let items, elem =
    match (Option.map T.resolve expected, es) with
    | Some (Con (item, [ t ])), _ when item = T.prelude_item "List" ->
        (List.map (check ctx t) es, t)
    | Some Error, _ -> (List.map (check ctx T.Error) es, T.Error)
    | _, [] -> ([], fresh st loc)
    | _, first :: rest ->
        let v = infer ctx None first in
        let elem = widen v.ty in
        subsume st first.loc ~expected:elem v.ty;
        (v :: List.map (check ctx elem) rest, elem)
  in
  node (List items) (T.list elem) loc

and index_expr ctx loc base index =
  let st = ctx.st in
  let b = infer ctx None base in
  match known st base.loc b.ty with
  | None ->
      ignore (abandon ctx index);
      error_node loc
  | Some (Con (item, [ t ])) when item = T.prelude_item "List" ->
      let i = check ctx T.i64 index in
      node (Index (b, i)) t loc
  (* generics.array-elements: an array is indexed as a list is. *)
  | Some t when Option.is_some (Check_arrays.parts t) ->
      let i = check ctx T.i64 index in
      node (Index (b, i)) (fst (Option.get (Check_arrays.parts t))) loc
  (* views.functions-of-views: a view of a list is indexed as the list is. *)
  | Some (Con ({ home = "std.view"; name = "View" }, [ list ]))
    when Option.is_some (list_element list) ->
      let i = check ctx T.i64 index in
      node (Index (b, i)) (Option.get (list_element list)) loc
  | Some (Con (item, [ k; v ])) when item = T.prelude_item "Map" ->
      (* std.map-key-bounds: indexing finds a key, as the map's methods do. *)
      obligation st k (prelude_trait "Eq") loc;
      obligation st k (prelude_trait "Hash") loc;
      let i = check ctx k index in
      node (Index (b, i)) v loc
  (* variadics.pack-tuples *)
  | Some t when Packs.has_spread t ->
      ignore (abandon ctx index);
      error st Code.e0342 loc
        "`%s` has as many elements as its pack, which this body doesn't know, \
         so it can't be indexed; map over it with a spread, as `(..e)`"
        (show t);
      error_node loc
  (* shared.std-sync: a [Shared<T>] is indexed only inside a [when]. *)
  | Some (Con ({ home = "std.sync"; name = "Shared" }, _) as t) ->
      ignore (abandon ctx index);
      error st Code.e0317 loc
        "a value of type `%s` can't be indexed: its value is reached only \
         inside a `when` that names it"
        (show t);
      error_node loc
  | Some t ->
      ignore (abandon ctx index);
      error st Code.e0317 loc "a value of type `%s` can't be indexed" (show t);
      error_node loc

and else_expr ctx loc a b = option_fallback ctx loc a (infer ctx None a) b

and raise_expr ctx loc value =
  let v = infer ctx None value in
  (* meta.fresh-types *)
  if Check_fresh.raised ctx.st v then
    perform ctx { T.empty_row with raise = Some v.ty } loc;
  node (Raise v) T.never loc

and return_expr ctx loc value =
  let v =
    match value with
    | Some value -> Some (check ctx ctx.ret value)
    | None ->
        expect ctx.st loc ~expected:ctx.ret T.unit;
        None
  in
  node (Return v) T.never loc
