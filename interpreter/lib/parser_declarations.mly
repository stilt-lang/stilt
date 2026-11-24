(* The declarations of the grammar of core Stilt: functions, types, traits,
   constants and tests, with the macros of parser_macros.mly, and the members of impls and traits. Menhir joins this
   file with parser.mly, whose header holds the helpers of the actions. *)

%%

(* Declarations *)

%public module_decl:
  | pub = boption(PUB) kind = pub_decl { node { pub; doc = []; kind; exported = false; foreign = false; unknown = false } $symbolstartpos }
  | kind = test_decl { node { pub = false; doc = []; kind; exported = false; foreign = false; unknown = false } $startpos }
  | PUB EXTERN e = extern_decl
    { let (f, foreign) = e in
      node { pub = true; exported = not foreign; foreign; doc = []; kind = Fn f; unknown = false } $symbolstartpos }
  | EXTERN h = fn_head w = option(without)
    { node { pub = false; exported = false; foreign = true; doc = []; kind = Fn (fn_decl h None w None); unknown = false } $symbolstartpos }

(* After [pub extern], a function's head alone, or with a [without] clause,
   declares a foreign function, which C gives (c.foreign-functions and
   c.effects), and one with a body is exported (c.exported-functions). Each
   form is spelled out, so that no empty [where] clause stands before a
   foreign function's [without]. *)
extern_decl:
  | h = fn_head { (fn_decl h None None None, true) }
  | h = fn_head w = without { (fn_decl h None (Some w) None, true) }
  | h = fn_head body = fn_body { (fn_decl h None None (Some body), false) }
  | h = fn_head w = without body = fn_body { (fn_decl h None (Some w) (Some body), false) }
  | h = fn_head wh = where_clause w = option(without) body = fn_body
    { (fn_decl h (Some wh) w (Some body), false) }

pub_decl:
  | f = fn_decl { Fn f }
  | t = type_decl { Type t }
  | t = trait_decl { t }
  | c = const_decl { Const c }
  | s = syntax_decl { s }
  | e = effect_decl { Effect e }
  | m = macro_decl { Macro m }

%public inherent_member:
  | doc = doc d = inherent_decl { documented doc d }

inherent_decl:
  | pub = boption(PUB) f = fn_decl
    { node { pub; doc = []; kind = Fn f; exported = false; foreign = false; unknown = false } $symbolstartpos }
  | pub = boption(PUB) c = const_decl
    { node { pub; doc = []; kind = Const c; exported = false; foreign = false; unknown = false } $symbolstartpos }

%public trait_impl_member:
  | doc = doc f = fn_decl
    { documented doc (node { pub = false; doc = []; kind = Fn f; exported = false; foreign = false; unknown = false } $startpos(f)) }
  | doc = doc c = const_decl
    { documented doc (node { pub = false; doc = []; kind = Const c; exported = false; foreign = false; unknown = false } $startpos(c)) }

(* In a trait, a function may leave out its body, and then its [without]
   clause, and a constant its value (traits.functions-without-self and traits.trait-constants). *)
trait_member:
  | doc = doc h = fn_head w = option(where_clause)
    { documented doc (node { pub = false; doc = []; kind = Fn (fn_decl h w None None); exported = false; foreign = false; unknown = false } $startpos(h)) }
  | doc = doc f = fn_decl
    { documented doc (node { pub = false; doc = []; kind = Fn f; exported = false; foreign = false; unknown = false } $startpos(f)) }
  | doc = doc CONST name = upper_name COLON ty = ty value = option(preceded(EQ, expr))
    { documented doc (node { pub = false; doc = []; kind = Const { name; ty; value }; exported = false; foreign = false; unknown = false } $startpos($2)) }

%public fn_decl:
  | h = fn_head wh = option(where_clause) w = option(without) body = fn_body
    { fn_decl h wh w (Some body) }

(* macros.procedural-declarations: a procedural macro, whose result is written, and whose
   generics, row and [without] clause are checked after parsing. *)
macro_decl:
  | MACRO name = lower_name generics = generics params = params
    ARROW ret = ty row = loption(preceded(SLASH, row)) w = option(without)
    b = block
    { fn_decl (name, generics, params, (false, Some ret), row) None w
        (Some (Body (b, loc $endpos))) }

(* A [where] clause bounds member types (traits.where). *)
%public where_clause:
  | WHERE bs = separated_nonempty_list(COMMA, where_bound) { node bs $startpos }

where_bound:
  | bounded = upper_path COLON bounds = bounds { { bounded; bounds } }

fn_head:
  | FN name = lower_name generics = generics params = params
    ret = result row = loption(preceded(SLASH, row))
    { (name, generics, params, ret, row) }

(* A result written [inout T] makes the function a projection (projections.declaring-projection). *)
result:
  | { (false, None) }
  | ARROW t = ty { (false, Some t) }
  | ARROW INOUT t = ty { (true, Some t) }

fn_body:
  | b = block { Body (b, loc $endpos) }
  | EQ QUESTION { Body_hole (loc $startpos($2)) }

(* Only functions declare row variables (effects.row-variables), and only functions
   and impl blocks take bounds (traits.bounds). *)
generics:
  | { [] }
  | LT gs = nonempty_comma_list(generic) GT { gs }
  | LT gs = generics_open GT_GT { gs }

(* Generics whose last bound or value parameter's type still needs one [>]:
   the first half of a [>>] that closes its arguments and the list at once,
   as in [<C: Collection<i64>>]. *)
generics_open:
  | p = type_param_open { [ Type_param p ] }
  | DOT_DOT p = type_param_open { [ Type_param (packed $startpos p) ] }
  | p = value_param_open { [ Type_param p ] }
  | g = generic COMMA gs = generics_open { g :: gs }

(* A pack, [..T], is a type parameter that stands for a sequence of types
   (variadics.packs). A lowercase name is a row variable, or with a type a
   value parameter (generics.value-parameters), which no [..] makes a pack (generics.value-parameter-positions). *)
generic:
  | p = type_param { Type_param p }
  | DOT_DOT p = type_param { Type_param (packed $startpos p) }
  | name = lower_name { Row_param name }
  | p = value_param { Type_param p }

(* An impl's generics: type parameters and value parameters (generics.value-parameters). *)
%public impl_generics:
  | { [] }
  | LT ps = nonempty_comma_list(impl_generic) GT { ps }
  | LT ps = type_params_open GT_GT { ps }

impl_generic:
  | p = type_param { p }
  | p = value_param { p }

type_params_open:
  | p = type_param_open { [ p ] }
  | p = value_param_open { [ p ] }
  | p = impl_generic COMMA ps = type_params_open { p :: ps }

(* A value parameter, [n: i64], whose type is checked after parsing (generics.value-parameters and generics.value-parameter-positions). *)
value_param:
  | name = lower_name COLON t = ty
    { { name; bounds = []; pack = false; value = Some t } }

value_param_open:
  | name = lower_name COLON t = ty_open
    { { name; bounds = []; pack = false; value = Some t } }

(* A function type's generics, among which a pack parses, to be reported
   after parsing (variadics.packs). *)
%public fn_generics:
  | { [] }
  | LT ps = nonempty_comma_list(fn_generic) GT { ps }
  | LT ps = fn_generics_open GT_GT { ps }

fn_generic:
  | p = type_param { p }
  | DOT_DOT p = type_param { packed $startpos p }

fn_generics_open:
  | p = type_param_open { [ p ] }
  | DOT_DOT p = type_param_open { [ packed $startpos p ] }
  | p = fn_generic COMMA ps = fn_generics_open { p :: ps }

type_param:
  | name = upper_name bounds = loption(preceded(COLON, bounds))
    { { name; bounds; pack = false; value = None } }

type_param_open:
  | name = upper_name COLON bounds = bounds_open
    { { name; bounds; pack = false; value = None } }

(* The parameters of a trait: names, of which none is a pack, which is an
   error after parsing (variadics.packs), and none a value parameter (generics.value-parameter-positions). *)
type_params:
  | { [] }
  | LT ps = nonempty_comma_list(type_name) GT { ps }

type_name:
  | name = upper_name { { name; bounds = []; pack = false; value = None } }
  | DOT_DOT name = upper_name
    { packed $startpos { name; bounds = []; pack = false; value = None } }

(* The parameters of a type: names, of which the last may be a pack (variadics.packs), and value parameters (generics.value-parameters). *)
type_decl_params:
  | { [] }
  | LT ps = nonempty_comma_list(type_decl_param) GT { ps }
  | LT ps = type_decl_params_open GT_GT { ps }

type_decl_param:
  | p = type_name { p }
  | p = value_param { p }

type_decl_params_open:
  | p = value_param_open { [ p ] }
  | p = type_decl_param COMMA ps = type_decl_params_open { p :: ps }

%public bounds:
  | b = bound { [ b ] }
  | b = bound PLUS bs = bounds { b :: bs }

(* A trait with all of its arguments or none (traits.bound-arguments), or the fields
   a record needs (records.record-bounds and records.bound-fields). *)
%public bound:
  | trait = upper_path { Trait_bound { trait; args = [] } }
  | trait = upper_path LT args = nonempty_comma_list(ty) GT
    { Trait_bound { trait; args } }
  | trait = upper_path LT args = ty_list_open GT_GT
    { Trait_bound { trait; args } }
  | LBRACE fs = record_fields RBRACE
    { Record_bound (node (Ty_record (fst fs, snd fs)) $startpos) }

(* Bounds whose last still needs one [>]. *)
bounds_open:
  | b = bound_open { [ b ] }
  | b = bound PLUS bs = bounds_open { b :: bs }

bound_open:
  | trait = upper_path LT args = nonempty_comma_list(ty)
    { Trait_bound { trait; args } }

params:
  | LPAREN ps = comma_list(param) RPAREN { ps }
  | LPAREN s = self_param RPAREN { [ s ] }
  | LPAREN s = self_param COMMA ps = comma_list(param) RPAREN { s :: ps }

self_param:
  | m = mode SELF { Self_param (m, loc $symbolstartpos, None) }
  | m = mode SELF COLON t = ty { Self_param (m, loc $symbolstartpos, Some t) }

(* An [escaping] parameter takes no mode, and its type is written with [fn]
   (declarations.parameters). *)
param:
  | m = mode name = lower_name COLON t = ty { Param (m, name, t, false) }
  | ESCAPING name = lower_name COLON t = fn_ty { Param (Let, name, t, true) }

%public mode:
  | { Let }
  | INOUT { Inout }

type_decl:
  | TYPE name = upper_name params = type_decl_params EQ def = type_def
    { { name; params; def } }

type_def:
  | LBRACE fields = comma_list(field_decl) RBRACE { Record fields }
  | PIPE vs = separated_nonempty_list(PIPE, variant) { Variants vs }
  | v = variant PIPE vs = separated_nonempty_list(PIPE, variant)
    { Variants (v :: vs) }
  | QUESTION { Native (loc $startpos) }

variant:
  | name = upper_name { { name; payload = [] } }
  | name = upper_name LPAREN payload = nonempty_comma_list(payload) RPAREN
    { { name; payload } }

payload:
  | t = ty { (None, t) }
  | n = lower_name COLON t = ty { (Some n, t) }

trait_decl:
  | TRAIT name = upper_name params = type_params
    LBRACE members = separated_list(SEP, trait_member) RBRACE
    { Trait { name; params; members } }

const_decl:
  | CONST name = upper_name COLON ty = ty EQ value = expr
    { { name; ty; value = Some value } }

(* An effect and its operations, each a function's head without generics or
   [inout] result (handlers.declaring-effect). *)
effect_decl:
  | EFFECT name = upper_name params = loption(delimited(LT, nonempty_comma_list(upper_name), GT))
    LBRACE ops = separated_list(SEP, operation) RBRACE
    { { name; params; ops } }

operation:
  | doc = doc FN name = lower_name params = params ret = option(preceded(ARROW, ty))
    row = loption(preceded(SLASH, row))
    { { op_doc = doc; op_name = name; op_params = params; op_ret = ret; op_row = row } }

test_decl:
  | TEST name = STRING body = block { Test (name, body) }
