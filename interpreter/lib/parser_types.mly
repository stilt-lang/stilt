(* The names, paths and types of the grammar of core Stilt. Menhir joins this
   file with parser.mly, whose header holds the helpers of the actions. *)

%%

(* Names and paths *)

%public lower_name:
  | n = LIDENT { node n $startpos }

%public upper_name:
  | n = UIDENT { node n $startpos }

%public lower_path:
  | n = lower_name { [ n ] }
  | p = lower_path DOT n = lower_name { p @ [ n ] }

(* The path of a [use]: a namespace's name, then names of either case, since
   name resolution tells a module from an item (program.what-use-binds). *)
%public use_path:
  | n = lower_name { [ n ] }
  | p = use_path DOT n = lower_name { p @ [ n ] }
  | p = use_path DOT n = upper_name { p @ [ n ] }

(* A path that ends in an uppercase name: [T], [m.T], [Self] or [T.NAME]. *)
%public upper_path:
  | n = upper_name { [ n ] }
  | SELF_TYPE { [ node "Self" $startpos ] }
  | p = lower_path DOT n = upper_name { p @ [ n ] }
  | p = upper_path DOT n = upper_name { p @ [ n ] }

(* Types *)

%public ty:
  | n = lower_name { node (Ty_named ([ n ], [])) $startpos }
  | p = upper_path { node (Ty_named (p, [])) $startpos }
  | p = upper_path LT args = nonempty_comma_list(ty) GT
    { node (Ty_named (p, args)) $startpos }
  | p = upper_path LT args = value_args GT
    { node (Ty_named (p, args)) $startpos }
  | p = upper_path LT args = ty_list_open GT_GT
    { node (Ty_named (p, args)) $startpos }
  | p = upper_path LT args = value_args_open GT_GT
    { node (Ty_named (p, args)) $startpos }
  | LPAREN ts = comma_list_t(elem_ty) RPAREN
    { parenthesized ~spread:is_spread_ty ~tuple:(fun ts -> Ty_tuple ts) ts $startpos }
  | LBRACE fs = record_fields RBRACE
    { node (Ty_record (fst fs, snd fs)) $startpos }
  | t = fn_ty { t }
  | t = handler_ty { t }
  (* macros.splices and macros.part-forms: a use of a macro whose result is a type, which
     takes no trailing block, and in a quote a splice. *)
  | p = lower_path g = macro_group { node (Ty_macro (p, g)) $startpos }
  | s = q_splice { node (Ty_splice s) $startpos }

(* A handler's type (handlers.handler-types), whose row is the next [/]'s unless an
   inner function or handler type takes it, as a function type's is. *)
handler_ty:
  | HANDLER e = effect_ref ret = option(preceded(ARROW, ty)) %prec below_slash
    { node (Ty_handler (e, ret, [])) $startpos }
  | HANDLER e = effect_ref ret = option(preceded(ARROW, ty)) SLASH r = row
    { node (Ty_handler (e, ret, r)) $startpos }

(* The effect of a handler, with its type arguments, or [async] (handlers.handler-types; tasks.async). *)
%public effect_ref:
  | p = upper_path { Effect_named (p, []) }
  | p = upper_path LT args = nonempty_comma_list(ty) GT { Effect_named (p, args) }
  | p = upper_path LT args = ty_list_open GT_GT { Effect_named (p, args) }
  | ASYNC { Effect_async (loc $startpos) }

(* The fields of an anonymous record type, which end with [..] in an open one
   (records.anonymous-types and records.open-parameter-types). *)
%public record_fields:
  | f = field_decl { ([ f ], false) }
  | f = field_decl COMMA { ([ f ], false) }
  | f = field_decl COMMA DOT_DOT { ([ f ], true) }
  | f = field_decl COMMA rest = record_fields { (f :: fst rest, snd rest) }

%public field_decl:
  | field = lower_name COLON ty = ty { { field; ty } }

(* A tuple type's element, or a function type's parameter, which may spread a
   pack (variadics.type-spreads). *)
elem_ty:
  | t = ty { t }
  | t = spread_ty { t }

spread_ty:
  | DOT_DOT t = ty { node (Ty_spread t) $startpos }

(* A function type, which an [escaping] parameter must have (declarations.parameters), and which may declare type parameters (polymorphism.function-types). A pack
   among them parses, and is an error after parsing (variadics.packs). *)
%public fn_ty:
  | FN gs = fn_generics LPAREN ps = comma_list(param_ty) RPAREN
    ret = option(preceded(ARROW, ty))
    %prec below_slash
    { node (Ty_fn (gs, ps, ret, [])) $startpos }
  | FN gs = fn_generics LPAREN ps = comma_list(param_ty) RPAREN
    ret = option(preceded(ARROW, ty)) SLASH r = row
    { node (Ty_fn (gs, ps, ret, r)) $startpos }

(* A literal given as a value argument, never computed (generics.value-arguments). A
   path among a type's arguments is a type to the grammar, and is read as a
   type or a value after parsing. *)
value_arg:
  | i = INT { node (Ty_int i) $startpos }
  | MINUS i = INT { node (Ty_int ("-" ^ i)) $startpos }
  | TRUE { node (Ty_bool true) $startpos }
  | FALSE { node (Ty_bool false) $startpos }

(* A named type's arguments, at least one of them a literal. The types before
   the first literal are read as every list of types is, so that an impl's
   type and its trait read alike up to it. *)
value_args:
  | v = value_arg { [ v ] }
  | v = value_arg COMMA { [ v ] }
  | v = value_arg COMMA ts = nonempty_comma_list(ty) { v :: ts }
  | v = value_arg COMMA ts = value_args { v :: ts }
  | t = ty COMMA ts = value_args { t :: ts }

(* Arguments with a literal whose last still needs one [>]. *)
value_args_open:
  | v = value_arg COMMA ts = ty_list_open { v :: ts }
  | v = value_arg COMMA ts = value_args_open { v :: ts }
  | t = ty COMMA ts = value_args_open { t :: ts }

(* A type that still needs one [>]: the first half of a [>>] that closes two
   lists of type arguments at once. The [<…>] of [raise] counts as one. *)
%public ty_open:
  | p = upper_path LT args = nonempty_comma_list(ty)
    { node (Ty_named (p, args)) $startpos }
  | p = upper_path LT args = value_args
    { node (Ty_named (p, args)) $startpos }
  | FN gs = fn_generics LPAREN ps = comma_list(param_ty) RPAREN ARROW
    ret = ty_open
    { node (Ty_fn (gs, ps, Some ret, [])) $startpos }
  | FN gs = fn_generics LPAREN ps = comma_list(param_ty) RPAREN
    ret = option(preceded(ARROW, ty)) SLASH RAISE LT t = ty
    { node (Ty_fn (gs, ps, ret, [ Row_raise (loc $startpos($7), t) ])) $startpos }
  | FN gs = fn_generics LPAREN ps = comma_list(param_ty) RPAREN
    ret = option(preceded(ARROW, ty)) SLASH p = upper_path LT args = nonempty_comma_list(ty)
    { node (Ty_fn (gs, ps, ret, [ Row_effect (p, args) ])) $startpos }
  | HANDLER p = upper_path LT args = nonempty_comma_list(ty)
    { node (Ty_handler (Effect_named (p, args), None, [])) $startpos }

%public ty_list_open:
  | t = ty_open { [ t ] }
  | t = ty COMMA ts = ty_list_open { t :: ts }

param_ty:
  | m = mode t = ty { (m, t) }
  | t = spread_ty { ((Let : mode), t) }

%public row:
  | e = row_elem { [ e ] }
  | LBRACE es = comma_list(row_elem) RBRACE { es }

row_elem:
  | IO { Row_io (loc $startpos) }
  (* handlers.effects-in-rows, and tasks.async *)
  | ASYNC { Row_async (loc $startpos) }
  | p = upper_path { Row_effect (p, []) }
  | p = upper_path LT args = nonempty_comma_list(ty) GT { Row_effect (p, args) }
  | p = upper_path LT args = ty_list_open GT_GT { Row_effect (p, args) }
  | n = lower_name { Row_var n }
  | RAISE LT t = ty GT { Row_raise (loc $startpos, t) }
  | RAISE LT t = ty_open GT_GT { Row_raise (loc $startpos, t) }
