(* The tree form of a syntax tree, as [stilt-ref parse --sexp] prints it:
   types, patterns and expressions, which a quote nests in one another
   (macros.splices), and declarations. *)

open Ast
open Sexp_atoms

(* Types *)

let unit_type = tagged "tuple" []

let rec ty (t : ty) =
  match t.desc with
  | Ty_named (p, []) -> path p
  | Ty_named (p, args) -> List (path p :: List.map ty args)
  (* generics.value-arguments: a literal argument is its atom. *)
  | Ty_int i -> Atom i
  | Ty_bool b -> Atom (string_of_bool b)
  | Ty_tuple ts -> tagged "tuple" (List.map ty ts)
  (* records.anonymous-types and records.open-parameter-types *)
  | Ty_record (fields, open_) ->
      tagged "record-type"
        (List.map field_type fields @ if open_ then [ Atom ".." ] else [])
  (* variadics.type-spreads *)
  | Ty_spread t -> tagged ".." [ ty t ]
  | Ty_fn (generics, params, ret, r) ->
      (* polymorphism.function-types: a polymorphic function type lists its generics
         first. *)
      tagged "fn"
        ((match generics with
           | [] -> []
           | gs -> [ List (List.map type_param gs) ])
        @ [
            List (List.map (fun (mode, t) -> with_mode mode (ty t)) params);
            return_type ret;
            row r;
          ])
  (* handlers.handler-types *)
  | Ty_handler (e, ret, r) ->
      tagged "handler" ((effect_ref e :: answer ret) @ [ row r ])
  (* macros.splices and macros.procedural-uses *)
  | Ty_macro (p, g) -> tagged "macro" [ path p; tree g ]
  | Ty_splice s -> expr s

(* A handler's effect: its path, the path with its arguments, or [async]. *)
and effect_ref = function
  | Effect_named (p, []) -> path p
  | Effect_named (p, args) -> List (path p :: List.map ty args)
  | Effect_async _ -> Atom "async"

and answer = function Some t -> [ tagged "->" [ ty t ] ] | None -> []
and return_type = function Some t -> ty t | None -> unit_type
and field_type ({ field; ty = t } : field_decl) = List [ name field; ty t ]

(* traits.bound-arguments: a bound is its path, or the path with its arguments, and a
   record bound its record type (records.record-bounds). *)
and bound = function
  | Trait_bound { trait; args = [] } -> path trait
  | Trait_bound { trait; args } -> List (path trait :: List.map ty args)
  | Record_bound t -> ty t

(* A pack is [(.. T)], with its bounds after its name (variadics.packs), and
   a value parameter [(value n T)] (generics.value-parameters). *)
and type_param = function
  | { name = n; value = Some t; _ } -> tagged "value" [ name n; ty t ]
  | { name = n; bounds = []; pack = false; value = None } -> name n
  | { name = n; bounds; pack = false; value = None } ->
      List (name n :: List.map bound bounds)
  | { name = n; bounds; pack = true; value = None } ->
      tagged ".." (name n :: List.map bound bounds)

and row elements =
  tagged "row"
    (List.map
       (function
         | Row_io _ -> Atom "io"
         | Row_raise (_, t) -> tagged "raise" [ ty t ]
         | Row_var n -> name n
         | Row_async _ -> Atom "async"
         | Row_effect (p, args) -> effect_ref (Effect_named (p, args)))
       elements)

(* Patterns *)

and pattern (p : pattern) =
  match p.desc with
  | P_wild -> Atom "_"
  | P_bind x -> Atom x
  | P_int i -> Atom i
  | P_str s -> str s
  | P_bool b -> Atom (string_of_bool b)
  | P_tuple ps -> tagged "tuple" (List.map pattern ps)
  | P_path p -> path p
  | P_variant (p, ps) -> List (path p :: List.map pattern ps)
  | P_record (p, fields, rest) ->
      record_pattern p (List.map (fun f -> Field_pattern f) fields) rest
  | P_spliced_record (p, fields, rest) -> record_pattern p fields rest
  | P_list (ps, rest) ->
      let rest =
        match rest with
        | Exact -> []
        | Rest -> [ Atom ".." ]
        | Rest_bind n -> [ tagged ".." [ name n ] ]
      in
      tagged "list" (List.map pattern ps @ rest)
  | P_or ps -> tagged "or" (List.map pattern ps)
  | P_macro (p, g) -> tagged "macro" [ path p; tree g ]
  (* macros.splices *)
  | P_splice s -> expr s

and record_pattern p fields rest =
  let fields =
    List.map
      (function
        | Field_pattern { field; pattern = p } -> List [ name field; pattern p ]
        | Spliced_field_pattern (s, p) -> List [ expr s; pattern p ])
      fields
  in
  (* records.anonymous-patterns: an anonymous record's pattern has [_] for its path. *)
  let p = match p with Some p -> path p | None -> Atom "_" in
  tagged "record" ((p :: fields) @ if rest then [ Atom ".." ] else [])

and annotated p = function
  | None -> pattern p
  | Some t -> tagged ":" [ pattern p; ty t ]

and expr (e : expr) =
  match e.desc with
  | Int i -> Atom i
  | Float f -> Atom f
  | Str s -> str s
  | Interpolated segments -> tagged "interp" (List.map segment segments)
  | Bool b -> Atom (string_of_bool b)
  | Name n -> Atom n
  | Self_value -> Atom "self"
  | Self_type -> Atom "Self"
  | Key_root -> Atom "."
  | Hole -> Atom "?"
  | Tuple es -> tagged "tuple" (List.map expr es)
  | List es -> tagged "list" (List.map expr es)
  | Field (e, m) -> tagged "field" [ expr e; name m ]
  | Call (f, args) -> tagged "call" (expr f :: List.map arg args)
  | Index (e, i) -> tagged "index" [ expr e; expr i ]
  | Struct (p, base, fields) ->
      tagged "struct" ((path p :: update base) @ List.map field_init fields)
  (* records.anonymous-literals and records.update *)
  | Record_literal (base, fields) ->
      tagged "record-lit" (update base @ List.map field_init fields)
  (* variadics.spread-expressions *)
  | Spread e -> tagged ".." [ expr e ]
  | Unary (Neg, e) -> tagged "neg" [ expr e ]
  | Unary (Not, e) -> tagged "not" [ expr e ]
  | Binary (op, a, b) -> tagged (binary op) [ expr a; expr b ]
  | Else (a, b) -> tagged "else" [ expr a; expr b ]
  | Try (e, None) -> tagged "try" [ expr e ]
  | Try (e, Some arms) ->
      tagged "try" [ expr e; tagged "catch" (List.map arm arms) ]
  | Raise e -> tagged "raise" [ expr e ]
  | Return None -> tagged "return" []
  | Return (Some e) -> tagged "return" [ expr e ]
  | Break -> Atom "break"
  | Continue -> Atom "continue"
  | Closure (params, body) ->
      tagged "closure" [ List (List.map closure_param params); expr body ]
  | Block b -> block b
  | If (cond, body, None) -> tagged "if" [ expr cond; block body ]
  | If (cond, body, Some e) -> tagged "if" [ expr cond; block body; expr e ]
  | If_let (p, e, body, alt) ->
      tagged "if"
        (tagged "let" [ pattern p; expr e ]
        :: block body
        :: Option.to_list (Option.map expr alt))
  | Match (e, arms) -> tagged "match" (expr e :: List.map arm arms)
  | Loop body -> tagged "loop" [ block body ]
  | While (cond, body) -> tagged "while" [ expr cond; block body ]
  | For (p, it, body) -> tagged "for" [ pattern p; iterable it; block body ]
  | Macro_use (p, groups) -> tagged "macro" (path p :: List.map tree groups)
  | Handler _ | With _ | Resume _ | When _ -> handling e
  (* meta.staging-annotations *)
  | Comptime e -> tagged "comptime" [ expr e ]
  (* c.unsafe-because *)
  | Unsafe (reason, body) -> tagged "unsafe" [ str reason.desc; block body ]
  (* meta.bound-tests *)
  | Bound_test (t, bounds) -> tagged "bound" (name t :: List.map bound bounds)
  | Quote { form; _ } -> quote_form form
  | Q_splice _ | Q_spread _ | Q_member _ | Q_record _ | Q_struct _ -> spliced e

(* macros.quote and macros.splices: quotes, and the splices and spreads in them. *)
and quote_form = function
  | Quote_block b -> tagged "quote" [ block b ]
  | Quote_type t -> tagged "quote-type" [ ty t ]
  | Quote_pattern p -> tagged "quote-pattern" [ pattern p ]
  | Quote_field f -> tagged "quote-field" [ spliced_field f ]

and spliced (e : expr) =
  match e.desc with
  | Q_splice e -> tagged "$" [ expr e ]
  | Q_spread e -> tagged "$.." [ expr e ]
  | Q_member (e, s) -> tagged "field" [ expr e; expr s ]
  | Q_record (base, fields) ->
      tagged "record-lit" (update base @ List.map spliced_field fields)
  | Q_struct (p, base, fields) ->
      tagged "struct" ((path p :: update base) @ List.map spliced_field fields)
  | _ -> invalid_arg "Sexp.spliced"

and spliced_field = function
  | Field_init f -> field_init f
  | Spliced_field (s, v) -> List [ expr s; expr v ]
  | Spread_fields s -> expr s

(* handlers.handler-literals, handlers.with and handlers.resuming, and shared.when *)
and handling (e : expr) =
  match e.desc with
  | Handler (e, ret, fns) ->
      tagged "handler"
        ((effect_ref e :: answer ret) @ List.map (fun f -> fn_decl f) fns)
  | With (handlers, body) ->
      tagged "with" [ List (List.map expr handlers); block body ]
  | Resume None -> tagged "resume" []
  | Resume (Some e) -> tagged "resume" [ expr e ]
  | When (names, body) ->
      tagged "when" [ List (List.map name names); block body ]
  | _ -> invalid_arg "Sexp.handling"

and update = function Some base -> [ tagged ".." [ expr base ] ] | None -> []

and segment = function
  | Text s -> str s
  | Splice (e, None) -> tagged "splice" [ expr e ]
  | Splice (e, Some spec) -> tagged "splice" [ expr e; str spec ]

and arg { inout; value } =
  if inout then tagged "inout" [ expr value ] else expr value

and field_init ({ field; value } : field_init) = List [ name field; expr value ]

and closure_param ({ mode; pattern = p; annotation } : closure_param) =
  match mode with
  | Let -> annotated p annotation
  | Inout ->
      tagged "inout" (pattern p :: Option.to_list (Option.map ty annotation))

and arm { pattern = p; guard; because; body } =
  let extra =
    match (guard, because) with
    | Some g, _ -> [ tagged "if" [ expr g ] ]
    | None, Some reason -> [ tagged "because" [ str reason.desc ] ]
    | None, None -> []
  in
  tagged "arm" ((pattern p :: extra) @ [ expr body ])

and iterable = function
  | Iter e -> expr e
  | Range (a, b, Exclusive) -> tagged ".." [ expr a; expr b ]
  | Range (a, b, Inclusive) -> tagged "..=" [ expr a; expr b ]

and block stmts = tagged "block" (List.map stmt stmts)

and stmt (s : stmt) =
  match s.desc with
  | Let b -> tagged "let" (binding b)
  | Var b -> tagged "var" (binding b)
  | Assign (None, place, value) -> tagged "=" [ expr place; expr value ]
  | Assign (Some op, place, value) ->
      tagged (binary op ^ "=") [ expr place; expr value ]
  | Assert e -> tagged "assert" [ expr e ]
  | Yield e -> tagged "yield" [ expr e ]
  | Expr e -> expr e

and binding ({ pattern = p; annotation; value } : binding) =
  [ annotated p annotation; expr value ]

(* traits.where *)
and where_clause (w : where_) =
  tagged "where"
    (List.map
       (fun ({ bounded; bounds } : where_bound) ->
         List (path bounded :: List.map bound bounds))
       w.desc)

and type_params ps = List (List.map type_param ps)
and generic = function Type_param p -> type_param p | Row_param n -> name n
and generics gs = List (List.map generic gs)

and param = function
  | Self_param (mode, _, None) -> with_mode mode (Atom "self")
  | Self_param (Let, _, Some t) -> List [ Atom "self"; ty t ]
  | Self_param (Inout, _, Some t) -> tagged "inout" [ Atom "self"; ty t ]
  | Param (_, n, t, true) -> tagged "escaping" [ name n; ty t ]
  | Param (mode, n, t, false) -> (
      match mode with
      | Let -> List [ name n; ty t ]
      | Inout -> tagged "inout" [ name n; ty t ])

and without (w : without) =
  tagged "without"
    (List.map
       (fun (l : limit node) -> Atom (Capability.limit_name l.desc))
       w.desc)

and fn_decl ?(tag = "fn") (f : fn_decl) =
  let body =
    match f.body with
    | None -> []
    | Some (Body (b, _)) -> [ block b ]
    | Some (Body_hole _) -> [ Atom "?" ]
  in
  tagged tag
    ([
       name f.name;
       generics f.generics;
       List (List.map param f.params);
       (if f.projection then tagged "inout" [ return_type f.ret ]
        else return_type f.ret);
       row f.row;
     ]
    @ Option.to_list (Option.map where_clause f.where_)
    @ Option.to_list (Option.map without f.without)
    @ body)

(* Declarations *)

let variant ({ name = n; payload } : variant_decl) =
  match payload with
  | [] -> name n
  | payload ->
      List
        (name n
        :: List.map
             (function
               | None, t -> ty t | Some field, t -> List [ name field; ty t ])
             payload)

(* handlers.declaring-effect: an effect, with [(params P…)] when it has type
   parameters, and its operations, each as a function's head. *)
let rec effect_decl ({ name = n; params; ops } : effect_decl) =
  let params =
    match params with [] -> [] | ps -> [ tagged "params" (List.map name ps) ]
  in
  tagged "effect" ((name n :: params) @ List.map operation ops)

and operation o =
  documented o.op_doc
    (tagged "op"
       [
         name o.op_name;
         List (List.map param o.op_params);
         return_type o.op_ret;
         row o.op_row;
       ])

and documented doc tree =
  match doc with
  | [] -> tree
  | lines ->
      tagged "doc"
        (List.map
           (function
             | Doc_text s -> str s
             | Doc_example e -> tagged "ex" [ expr e ]
             | Doc_property (_, e) -> tagged "prop" [ expr e ])
           lines
        @ [ tree ])

and decl ({ pub; exported; foreign; doc; kind; _ } : decl) =
  let tree =
    match kind with
    | Fn f -> fn_decl f
    | Type { name = n; params; def = Record fields } ->
        tagged "type"
          [
            name n;
            List (List.map type_param params);
            tagged "record" (List.map field_type fields);
          ]
    | Type { name = n; params; def = Variants vs } ->
        tagged "type"
          [
            name n;
            List (List.map type_param params);
            tagged "variants" (List.map variant vs);
          ]
    | Type { name = n; params; def = Native _ } ->
        (* views.std-view: a native type's representation is [?], as a native
           function's body is. *)
        tagged "type" [ name n; List (List.map type_param params); Atom "?" ]
    | Trait { name = n; params; members } ->
        let params =
          match params with
          | [] -> []
          | ps -> [ tagged "params" (List.map type_param ps) ]
        in
        tagged "trait" ((name n :: params) @ List.map member members)
    | Const { name = n; ty = t; value } ->
        tagged "const"
          ([ name n; ty t ] @ Option.to_list (Option.map expr value))
    | Test (n, body) -> tagged "test" [ str n; block body ]
    | Syntax { name = n; arms } ->
        tagged "syntax" (name n :: List.map macro_arm arms)
    | Effect e -> effect_decl e
    (* macros.procedural-declarations *)
    | Macro f -> fn_decl ~tag:"macro-decl" f
  in
  let tree = if exported || foreign then tagged "extern" [ tree ] else tree in
  let tree = if pub then tagged "pub" [ tree ] else tree in
  documented doc tree

and member (m : decl node) = decl m.desc

let item (i : item) =
  match i.desc with
  | Use p -> tagged "use" [ path p ]
  | Meta_use p -> tagged "meta-use" [ path p ]
  | Decl d -> decl d
  | Impl { generics = ps; trait_ = None; self_ty; where_; members } ->
      tagged "impl"
        ([ type_params ps; ty self_ty ]
        @ Option.to_list (Option.map where_clause where_)
        @ List.map member members)
  | Impl { generics = ps; trait_ = Some tr; self_ty; where_; members } ->
      tagged "impl-trait"
        ([ type_params ps; bound tr; ty self_ty ]
        @ Option.to_list (Option.map where_clause where_)
        @ List.map member members)

let header (h : header node) =
  tagged "header" (path h.desc.path :: List.map without h.desc.withouts)

let of_module (m : module_) =
  let header = Option.to_list (Option.map header m.header) in
  to_string (tagged "module" (header @ List.map item m.items))

let of_expr e = to_string (expr e)
let binary = binary
let quote = quote
