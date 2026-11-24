(* Declarations: functions, constants, types, traits and impl blocks, and the
   bodies they hold (traits.impl-blocks and traits.declaring-trait). *)

open Hir
open Resolve_context
open Resolve_types
open Resolve_generics
open Resolve_patterns
open Resolve_exprs

(* lexical.primitive-type-names *)
let check_not_primitive ctx (n : name) =
  if is_primitive n.desc then
    errorf ctx Code.e0210 n.loc "`%s` is a primitive type name" n.desc

(* Reports each name in [names] that an earlier one repeats, for names
   declared together inside a declaration. *)
let check_unique ctx what (names : name list) =
  ignore
    (List.fold_left
       (fun seen (n : name) ->
         if Sset.mem n.desc seen then (
           errorf ctx Code.e0208 n.loc "`%s` is already %s here" n.desc what;
           seen)
         else Sset.add n.desc seen)
       Sset.empty names)

(* Resolves the body known by [loc], recording it when that reports an
   error. *)
let body ctx (loc : loc) resolve =
  let st = ctx.env.st in
  let before = st.diagnostics and held = st.held in
  let resolved = in_body st ~file:ctx.scope.file ~at:loc resolve in
  if st.diagnostics != before || st.held != held then
    st.unresolved <- (ctx.scope.file, loc) :: st.unresolved;
  resolved

(* An example's names resolve as in a test body of its module (program.doc-examples), and so do a property's (tests.property-checking). *)
let resolve_doc ctx doc =
  let ctx = module_ctx ctx.env ctx.scope in
  List.map
    (function
      | Ast.Doc_text s -> Doc_text s
      | Doc_example e ->
          Doc_example (body ctx e.loc (fun () -> resolve_expr ctx e))
      | Doc_property (text, e) ->
          Doc_property (text, body ctx e.loc (fun () -> resolve_expr ctx e)))
    doc

(* The first row variable written in [t], at any depth. [panic] and [alloc]
   are effect names, which E0501 reports (effects.effect-names). *)
let rec written_row_var (t : Ast.ty) =
  let first f xs = List.find_map f xs in
  match t.desc with
  | Ty_named (_, args) -> first written_row_var args
  | Ty_int _ | Ty_bool _ | Ty_macro _ | Ty_splice _ -> None
  | Ty_tuple ts -> first written_row_var ts
  | Ty_record (fields, _) ->
      first (fun (f : Ast.field_decl) -> written_row_var f.ty) fields
  | Ty_spread t -> written_row_var t
  | Ty_fn (_, params, ret, row) -> (
      (* In the order they are written: the parameters, the result, then the
         row (E0509's span is the first written). *)
      match
        first written_row_var (List.map snd params @ Option.to_list ret)
      with
      | Some n -> Some n
      | None ->
          first
            (function
              | Ast.Row_var (n : name)
                when not (List.mem n.desc Resolve_types.implicit_effects) ->
                  Some n
              | _ -> None)
            row)
  | Ty_handler (e, ret, row) -> (
      let args = match e with Effect_named (_, args) -> args | _ -> [] in
      match first written_row_var (args @ Option.to_list ret) with
      | Some n -> Some n
      | None ->
          first
            (function
              | Ast.Row_var (n : name)
                when not (List.mem n.desc Resolve_types.implicit_effects) ->
                  Some n
              | _ -> None)
            row)

(* effects.row-variables: a non-escaping parameter, one of function type that is
   neither [inout] nor written [escaping] (effects.non-escaping-parameters), writes no row variable in
   its type, which is then the error type. *)
let param_type ctx signature mode (n : name) (t : Ast.ty) escaping =
  match ((mode : Ast.mode), escaping, t.desc) with
  (* handlers.handler-types: as is one of handler type. *)
  | Let, false, (Ty_fn _ | Ty_handler _) -> (
      match written_row_var t with
      | Some v ->
          errorf ctx Code.e0509 v.loc
            "`%s` passes its effects through, so its type writes no row \
             variable: leave `%s` out, or write `escaping %s`"
            n.desc v.desc n.desc;
          { desc = Ty_error; loc = t.loc }
      | None -> resolve_ty ~poly:true signature t)
  | _ -> resolve_ty ~poly:true signature t

(* traits.receiver-types: a method of a constructor trait, or of an impl of one,
   writes its receiver's type, and no other method does. *)
let receiver_type ctx signature loc (t : Ast.ty option) =
  match t with
  | None when ctx.ctor > 0 ->
      errorf ctx Code.e0338 loc
        "a method of a trait over type constructors writes its receiver's \
         type, as `self: Self<A>`";
      None
  | None -> None
  | Some t when ctx.ctor > 0 -> Some (resolve_ty signature t)
  | Some _ ->
      errorf ctx Code.e0338 loc
        "a receiver's type is `Self`, which isn't written: write `self`";
      None

(* records.open-parameter-types: an open record type as a parameter's type stands for a
   type parameter of the function, hidden and unnamed, with that record
   bound, which [hidden] collects. *)
let open_param ctx signature hidden (t : Ast.ty) fields =
  advanced ctx;
  let name =
    "{ "
    ^ String.concat ", "
        (List.map (fun (f : Ast.field_decl) -> f.field.desc) fields)
    ^ ", .. }"
  in
  let var = fresh ctx { desc = name; loc = t.loc } in
  let fields = record_fields signature fields in
  hidden :=
    !hidden
    @ [
        { var; bounds = []; fields; pack = false; implied = true; value = None };
      ];
  { desc = Ty_param var; loc = t.loc }

let resolve_fn ctx ~public ~methods (f : Ast.fn_decl) : fn_decl =
  let signature, generics = declare_generics { ctx with public } f.generics in
  let generics, where_bounds = where_generics signature f.where_ generics in
  let hidden = ref [] in
  let b = binder () in
  let param : Ast.param -> param = function
    | Self_param (mode, loc, t) ->
        if not methods then
          errorf ctx Code.e0215 loc
            "only functions in impl and trait blocks take `self`";
        let t = receiver_type ctx signature loc t in
        let v = fresh ctx { desc = "self"; loc } in
        b.bound <- ("self", v) :: b.bound;
        Self_param (mode, v, t)
    | Param (mode, n, ({ desc = Ty_record (fields, true); _ } as t), escaping)
      ->
        let t = open_param ctx signature hidden t fields in
        Param (mode, bind signature b n, t, escaping)
    | Param (mode, n, t, escaping) ->
        let t = param_type ctx signature mode n t escaping in
        Param (mode, bind signature b n, t, escaping)
  in
  let params = List.map param f.params in
  let generics = generics @ List.map (fun p -> Type_param p) !hidden in
  let ret = Option.map (resolve_ty signature) f.ret in
  Resolve_determined.check ctx generics f (params, ret);
  let row = resolve_row signature f.row in
  (* projections.cannot-raise: a projection's call is a place, which no [try] can
     mark, so its row holds no [raise<E>]; one written is an error, and
     then no part of the row (errors.error-type). *)
  let row = if f.projection then { row with raise = None } else row in
  (* projections.declaring-projection: a module that declares a projection is in the advanced
     tier. *)
  if f.projection then advanced ctx;
  if f.projection then
    List.iter
      (function
        | Ast.Row_raise (loc, _) ->
            errorf ctx Code.e0427 loc
              "a projection's call is a place, which can't sit in a `try`, so \
               its row can't hold `raise`; panic instead, or have the caller \
               check first"
        | Row_io _ | Row_var _ | Row_effect _ | Row_async _ -> ())
      f.row;
  let body_ctx = { (with_bound signature b) with public = false } in
  let body =
    Option.map
      (function
        | Ast.Body (block, close) ->
            Body
              ( body ctx f.name.loc (fun () -> resolve_block body_ctx block),
                close )
        | Body_hole loc -> Body_hole loc)
      f.body
  in
  let limits = Resolve_limits.of_fn ctx f.without in
  let projection = f.projection in
  let name = f.name in
  { name; generics; params; ret; projection; row; limits; body; where_bounds }

let resolve_const ctx ~public (c : Ast.const_decl) : const_decl =
  let ty = resolve_ty { ctx with public } c.ty in
  {
    name = c.name;
    ty;
    value =
      Option.map
        (fun value -> body ctx c.name.loc (fun () -> resolve_expr ctx value))
        c.value;
  }

(* variadics.packs: a type declares at most one pack, as its last parameter,
   so that its arguments say where the pack starts (E0344). Tells whether
   its packs are well placed; if not, each is a plain type parameter after
   E0344, so that nothing more is reported of it. *)
let type_packs ctx (params : Ast.type_param list) =
  match List.filter (fun (p : Ast.type_param) -> p.pack) params with
  | [] -> true
  | [ p ] ->
      let last = (List.nth params (List.length params - 1)).pack in
      if not last then
        errorf ctx Code.e0344 p.name.loc
          "a pack is a type's last parameter, so that the arguments after the \
           others are the pack's";
      last
  | _ :: more ->
      List.iter
        (fun (p : Ast.type_param) ->
          errorf ctx Code.e0344 p.name.loc
            "a type declares at most one pack, so that its arguments say where \
             the pack starts")
        more;
      false

let resolve_type_decl ctx ~public (t : Ast.type_decl) : type_decl =
  let placed = type_packs ctx t.params in
  if List.exists (fun (p : Ast.type_param) -> p.pack) t.params then advanced ctx;
  let ctx, params =
    List.fold_left
      (fun (ctx, params) (p : Ast.type_param) ->
        match p.value with
        (* generics.value-parameters: a value parameter, which may appear in none of the
           type's fields (generics.value-parameters-determined). *)
        | Some t ->
            let ctx, param = Resolve_generics.declare_value ctx p.name t in
            (ctx, param.var :: params)
        | None ->
            let v, type_params =
              declare ctx ctx.type_params "a type parameter" p.name
            in
            let ctx =
              match (p.pack, placed) with
              | true, true -> { ctx with packs = v.id :: ctx.packs }
              | true, false -> { ctx with misplaced = v.id :: ctx.misplaced }
              | false, _ -> ctx
            in
            ({ ctx with type_params }, v :: params))
      ({ ctx with public }, [])
      t.params
  in
  let def =
    match t.def with
    | Record fields ->
        let names = List.map (fun (f : Ast.field_decl) -> f.field) fields in
        List.iter (check_not_primitive ctx) names;
        check_unique ctx "a field" names;
        Record
          (List.map
             (fun ({ field; ty } : Ast.field_decl) ->
               { field; ty = resolve_ty ~poly:true ctx ty })
             fields)
    | Variants variants ->
        let variant ({ name; payload } : Ast.variant_decl) =
          List.iter
            (fun (n, _) -> Option.iter (check_not_primitive ctx) n)
            payload;
          {
            name;
            payload =
              List.map (fun (_, t) -> resolve_ty ~poly:true ctx t) payload;
          }
        in
        Variants (List.map variant variants)
    | Native _ -> Native
  in
  { name = t.name; params = List.rev params; def }

(* The grammar puts only functions and constants in impl and trait blocks. *)
let member_name (d : Ast.decl Ast.node) =
  match d.desc.kind with
  | Fn f -> f.name
  | Const c -> c.name
  | Type _ | Trait _ | Test _ | Syntax _ | Effect _ | Macro _ ->
      invalid_arg "Resolve.member_name"

(* The resolved declaration of [d], whose kind resolves to [kind]. *)
let resolved ctx (d : Ast.decl Ast.node) kind : decl node =
  let { Ast.pub; exported; foreign; doc; unknown; _ } = d.desc in
  (* c.systems-tier: a foreign function makes its module systems. *)
  if foreign then systems ctx;
  let doc = resolve_doc ctx doc in
  { desc = { pub; exported; foreign; doc; kind; unknown }; loc = d.loc }

let resolve_member ctx ~public (d : Ast.decl Ast.node) : decl node =
  resolved ctx d
    (match d.desc.kind with
    | Fn f -> Fn (resolve_fn ctx ~public ~methods:true f)
    | Const c -> Const (resolve_const ctx ~public c)
    | Type _ | Trait _ | Test _ | Syntax _ | Effect _ | Macro _ ->
        invalid_arg "Resolve.resolve_member")

(* A trait, whose parameters are in scope in its members (traits.trait-parameters),
   and whose [Self] takes the arguments of its arity (traits.constructor-traits). *)
let resolve_trait ctx ~public (t : Ast.trait_decl) : trait_decl =
  let names = List.map member_name t.members in
  List.iter (check_not_primitive ctx) names;
  check_unique ctx "a member of this trait" names;
  let shape = Resolve_scopes.trait_entry public t in
  if shape.advanced then advanced ctx;
  let ctx, params =
    List.fold_left
      (fun (ctx, params) (p : Ast.type_param) ->
        (* variadics.packs *)
        if p.pack then
          errorf ctx Code.e0344 p.name.loc
            "a trait's parameters are never packs";
        let v, type_params =
          declare ctx ctx.type_params "a type parameter" p.name
        in
        let misplaced =
          if p.pack then v.id :: ctx.misplaced else ctx.misplaced
        in
        ({ ctx with type_params; misplaced }, params @ [ v ]))
      (ctx, []) t.params
  in
  let ctx = { ctx with self = Trait_self; ctor = shape.arity; fixed = true } in
  {
    name = t.name;
    params;
    arity = shape.arity;
    members = List.map (resolve_member ctx ~public) t.members;
  }

let resolve_decl ctx (d : Ast.decl Ast.node) : decl node =
  let pub = d.desc.pub in
  resolved ctx d
    (match d.desc.kind with
    | Fn f -> Fn (resolve_fn ctx ~public:pub ~methods:false f)
    | Type t -> Type (resolve_type_decl ctx ~public:pub t)
    | Trait t -> Trait (resolve_trait ctx ~public:pub t)
    | Const c -> Const (resolve_const ctx ~public:pub c)
    | Test (name, block) ->
        Test (name, body ctx d.loc (fun () -> resolve_block ctx block))
    | Effect e -> Effect (Resolve_effects.resolve_effect ctx ~public:pub e)
    (* A macro is no declaration of the resolved program: its uses are
       expanded where they are (macros.expansion). A procedural macro is a
       function of the program (macros.procedural-bodies). *)
    | Syntax _ | Macro _ -> invalid_arg "Resolve.resolve_decl")

(* traits.constructor-impls: an impl of a constructor trait is for a constructor of
   its arity, written without arguments or type parameters. Another is E0337,
   and its members have no trait, so they aren't checked against it. *)
let impl_type ctx arity (i : Ast.impl_decl) trait_ =
  let trait_ = Option.map (fun (r : resolved_bound) -> r.bound) trait_ in
  if arity = 0 then (resolve_ty ctx i.self_ty, trait_)
  else
    let broken t = (t, Some { trait = Trait_error; args = [] }) in
    match i.generics with
    | p :: _ ->
        errorf ctx Code.e0337 p.name.loc
          "an impl of a trait over type constructors has no type parameters";
        broken { desc = Ty_error; loc = i.self_ty.loc }
    | [] -> (
        match constructor ctx arity i.self_ty with
        | { desc = Ty_error; _ } as t -> broken t
        | t -> (t, trait_))

(* Other modules see the signature of a [pub] member of an inherent impl of a
   [pub] type, and so the block's generics when it has such a member (program.private-in-signatures). The type of an inherent impl is one of its module's own types
   (traits.impl-blocks), named by a single name. A trait impl's methods have the
   trait's signatures. *)
let resolve_impl ctx (i : Ast.impl_decl) : impl_decl =
  let public_type =
    Option.is_none i.trait_
    &&
    match i.self_ty.desc with
    | Ty_named ([ n ], _) -> (
        match Smap.find_opt n.desc ctx.scope.types with
        | Some e -> e.pub
        | None -> false)
    | _ -> false
  in
  let public =
    public_type
    && List.exists (fun (d : Ast.decl Ast.node) -> d.desc.pub) i.members
  in
  let outer = ctx.type_params in
  let ctx, generics = declare_impl_generics { ctx with public } i.generics in
  let trait_ = Option.map (resolve_bound ctx) i.trait_ in
  let arity = match trait_ with Some r -> r.arity | None -> 0 in
  let self_ty, trait_ = impl_type ctx arity i trait_ in
  let generics, where_bounds = resolve_where ctx i.where_ generics in
  let names = List.map member_name i.members in
  List.iter (check_not_primitive ctx) names;
  if Option.is_some trait_ then check_unique ctx "a member of this impl" names;
  let ctx =
    {
      ctx with
      self = Impl_self self_ty;
      ctor = arity;
      fixed = Option.is_some trait_;
    }
  in
  let member (d : Ast.decl Ast.node) =
    (* declarations.impl-constants: a constant is the same for every type argument, so
       its type names neither the block's type parameters nor [Self]. A trait
       impl's constant has the type the trait gives it, with one value for
       the impl (traits.trait-constants). *)
    let ctx =
      match d.desc.kind with
      | Const _ when generics <> [] && Option.is_none trait_ ->
          { ctx with type_params = outer; value_params = []; self = No_self }
      | _ -> ctx
    in
    resolve_member ctx ~public:(public_type && d.desc.pub) d
  in
  {
    generics;
    trait_;
    self_ty;
    where_bounds;
    members = List.map member i.members;
  }

(* traits.inherent-names: a name is defined at most once across the inherent impl
   blocks of a type. Only blocks in the type's home module count, since only
   they are allowed. *)
let check_inherent_members ctx (impls : impl_decl list) =
  let names (i : impl_decl) =
    List.map
      (fun (d : decl node) ->
        match d.desc.kind with
        | Fn f -> f.name
        | Const c -> c.name
        | Type _ | Trait _ | Test _ | Effect _ -> invalid_arg "Resolve.names")
      i.members
  in
  let members =
    List.fold_left
      (fun members (i : impl_decl) ->
        match (i.trait_, i.self_ty.desc) with
        | None, Ty_con (item, _) when item.home = ctx.scope.name ->
            Smap.update item.name
              (fun earlier -> Some (Option.value earlier ~default:[] @ names i))
              members
        | _ -> members)
      Smap.empty impls
  in
  Smap.iter
    (fun _ names -> check_unique ctx "a member of this type" names)
    members
