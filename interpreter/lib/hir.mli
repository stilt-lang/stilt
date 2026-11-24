(** The program after name resolution.

    The tree follows {!Ast}, except that every name refers to what it names
    (program.namespaces, declarations.name-lookup):
    - a name in an expression is a local variable, an item, or a member of a
      type or trait;
    - a name in a type is an item or a type parameter, and [Self] inside an
      [impl] block is the block's type;
    - a name in a pattern is a variable, a variant, a constant or a record type,
      but for a variant or a constant written without a module, which keeps what
      it means in scope for the type checker, which reads it through the type
      the pattern is matched against (patterns.variants-by-type).

    A name that fails to resolve becomes an error node, which the type checker
    gives the error type (errors.error-type and errors.unknown-names). Fields
    and methods of values are left as [Field] for the type checker, which needs
    the receiver's type. *)

type loc = Ast.loc = { line : int; col : int }
type 'a node = 'a Ast.node = { desc : 'a; loc : loc }
type name = string node
type mode = Ast.mode

type item = { home : string; name : string }
(** A module-level item: its home module and its own name, unique in its
    namespace there (declarations.unique-names); a built-in type is
    [std.prelude]'s. *)

type var = { id : int; name : string; loc : loc }
(** A variable: a local binding, a type parameter or a row variable. Each
    declaration has an [id] that no other declaration in the program has, and
    every use refers to it. *)

(** A trait, as a bound or as the trait of an impl. *)
type trait_ref =
  | Trait_ref of item
  | Trait_error
      (** A trait name with an error, which the type checker treats as satisfied
          by every type. *)

(** {1 Types} *)

type ty = ty_desc node

and ty_desc =
  | Ty_con of item * ty list
      (** A named type with its arguments, such as [i64] or [List<Order>]. *)
  | Ty_param of var
      (** A type parameter, or a value parameter given as a value argument. *)
  | Ty_value of string
      (** A value argument that is a literal or a constant: its value, in
          decimal, or [true] or [false], so that two are one exactly when their
          values are (generics.value-arguments and generics.equal-types). *)
  | Ty_self  (** [Self] in a trait: the type that implements it. *)
  | Ty_app of var * ty list
      (** A constructor parameter applied to its arguments, as [F<i64>]. *)
  | Ty_self_app of ty list
      (** [Self<A>] in a constructor trait: the constructor that implements it,
          applied. *)
  | Ty_tuple of ty list  (** [()] is the empty tuple. *)
  | Ty_record of field_decl list
      (** An anonymous record type, with its fields as written
          (records.anonymous-types). An open one is a parameter's hidden type
          parameter (records.open-parameter-types). *)
  | Ty_spread of var * ty
      (** [..T], among a tuple type's elements or a function type's parameters:
          the one pack that [T] names, and [T] (variadics.type-spreads). *)
  | Ty_fn of type_param list * (mode * ty) list * ty option * row
      (** Its type parameters, which only a polymorphic function type has,
          parameters, return type and row. *)
  | Ty_handler of effect_inst * ty option * row
      (** A handler's type: its effect, the [R] of one that takes control, and
          its row. *)
  | Ty_error  (** A type with an error. *)

and row = {
  io : bool;
  raise : ty option;
  var : var option;
  effects : effect_inst list;
      (** Its effects, each once, [async] among them (handlers.effects-in-rows;
          tasks.async). *)
}
(** An effect row, each kind of element in it at most once. *)

and effect_inst = { eff : item; args : ty list; at : loc }
(** An effect with its type arguments, where it is written. [async] is the
    effect [Types.async_effect]. *)

and bound = { trait : trait_ref; args : ty list }
(** A bound with the trait's arguments, one for each of its parameters
    (traits.bound-arguments). A bound written without them has one implied type
    parameter for each, which its member types name. *)

and field_decl = { field : name; ty : ty }

and type_param = {
  var : var;
  bounds : bound list;
  fields : field_decl list;
      (** The fields of its record bounds, which a record it stands for has, and
          none without one. *)
  pack : bool;  (** Whether it is a pack. *)
  implied : bool;
      (** Whether it is the implied parameter of a member type, such as
          [C.Item], or of an open record type, which no generic list writes
          (traits.member-types; records.open-parameter-types). *)
  value : ty option;
      (** For a value parameter, its type: an integer type or [bool], or the
          error type (generics.value-parameters). It has no bounds and is no
          pack. *)
}

(** {1 Patterns} *)

type pattern = pattern_desc node

and pattern_desc =
  | P_wild
  | P_bind of var
  | P_int of string
  | P_str of string
  | P_bool of bool
  | P_tuple of pattern list
  | P_const of item  (** A constant, written [C] or [m.C]. *)
  | P_assoc_const of ty * name  (** A constant of a type, [Type.NAME]. *)
  | P_variant of item * pattern list
      (** A variant with its payload patterns, which are none for [None]. *)
  | P_bare of name * pattern list * fallback
      (** A name without a module, [V] or [V(p₁, …)], with its payload patterns.
          It names the variant [V] of the type the pattern is matched against,
          when that type has one, and otherwise its [fallback]
          (patterns.variants-by-type). *)
  | P_record of ty * field_pattern list * bool
      (** The record type, the fields, and whether [..] ends the list. *)
  | P_fields of field_pattern list * bool
      (** [{ f, g: p }], which matches the record type the pattern is matched
          against, with whether [..] ends it (records.anonymous-patterns). *)
  | P_list of pattern list * list_rest
  | P_or of pattern list
      (** Two or more alternatives, which bind the same variables. *)
  | P_error

and field_pattern = { field : name; pattern : pattern }
and list_rest = Exact | Rest | Rest_bind of var

(** What a name without a module means in a pattern where the type matched has
    no variant of that name: what it means in the module's scope. *)
and fallback =
  | Scope_variant of item
  | Scope_const of item
  | Scope_error  (** A name whose uses have the error type. *)
  | Scope_failure of Diagnostic.t
      (** A name that means no variant or constant there, and its error: E0211
          when it means nothing, E0212 when it means something else. *)

(** {1 Expressions and statements} *)

(** The code that a quote writes, or a macro gives. *)
type code = Code_expr | Code_type | Code_pattern | Code_field

(** Where a splice stands in a quote: as an expression, a pattern, a type or a
    name, or spread among elements or a record's fields (macros.splices). *)
type place =
  | In_expr
  | In_pattern
  | In_type
  | In_name
  | In_elements
  | In_fields

type expr = expr_desc node

and expr_desc =
  | Int of string
  | Float of string
  | Str of string
  | Interpolated of segment list
  | Bool of bool
  | Local of var  (** A local binding or parameter, [self] included. *)
  | Value_param of var * ty
      (** A value parameter read in a body, with its type. *)
  | Func of item
  | Const of item
  | Variant of item
  | Member of owner * name
      (** [Type.f], [Type.NAME] or [Trait.m], which the type checker looks up.
      *)
  | Key_root
  | Hole
  | Tuple of expr list
  | List of expr list
  | Field of expr * name
  | Call of expr * arg list
  | Index of expr * expr
  | Struct of ty * expr option * field_init list
      (** A struct literal, or an update with its base. *)
  | Record_literal of expr option * field_init list
      (** An anonymous record literal, or an update of a record that isn't
          named. *)
  | Spread of expr  (** [..e]. *)
  | Unary of Ast.unary * expr
  | Binary of Ast.binary * expr * expr
  | Else of expr * expr
  | Try of expr * arm list option
  | Raise of expr
  | Return of expr option
  | Break
  | Continue
  | Closure of closure_param list * expr
  | Block of block
  | If of expr * block * expr option
  | If_let of pattern * expr * block * expr option
      (** The pattern's variables are in scope in the first block only. *)
  | Match of expr * arm list
  | Loop of block
  | While of expr * block
  | For of pattern * iterable * block
  | Perform of item * name
      (** [Effect.op], an operation of an effect, which a call performs. *)
  | Handler of handler_lit  (** A handler literal. *)
  | With of expr list * block  (** [with h₁, h₂ { … }]. *)
  | Resume of expr option  (** [resume(v)]. *)
  | When of (expr * var) list * block
      (** [when a, b { … }]: each name as it is resolved outside, with the
          binding that stands for its value's place in the block (shared.when).
      *)
  | Comptime of expr
      (** A staging annotation of an [If], an [If_let], a [Match] or a [For]. *)
  | Unsafe of block  (** An [unsafe] block, at its [unsafe]. *)
  | Bound_test of var * bound list
      (** [T: B + …] on the type parameter [T] in scope, the whole condition of
          an [If]. *)
  | Quote of quote  (** A quote. *)
  | Error
      (** A name with an error, one whose uses have the error type, or a [break]
          or [continue] outside every loop. *)

and handler_lit = {
  heffect : effect_inst option;
      (** Its effect, or [None] for none, which resolution reported. *)
  async_at : loc option;
      (** The [handler] of a literal of [async], which only [std.task] gives. *)
  answer : ty option;  (** The [R] of a handler that takes control. *)
  ops : handler_op list;
}

and handler_op = {
  op_name : name;
  op_params : (mode * var * ty) list;
  op_ret : ty option;
  op_row : row;
  op_plain : bool;
      (** Whether it is written as an operation's head is: no generics,
          receiver, [inout] result, [where] or [without]. *)
  op_body : block;  (** Its body, or a hole for one written [= ?]. *)
}

and owner = Of_type of ty | Of_trait of item

and quote = {
  home : string;  (** Its module, where its names resolve. *)
  form : code;
  tokens : Ast.tree list;  (** Its contents, as written. *)
  splices : splice list;  (** In the order of their [$]. *)
  names : (item * loc) list;  (** As a macro's [names], its quotes' too. *)
}
(** A quote, kept as tokens that its run fills (macros.quote, macros.splices and
    macros.quote-hygiene). *)

and splice = {
  place : place;
  spread : bool;  (** Whether it is a spread, [$..x]. *)
  at : loc;  (** Its [$]. *)
  value : expr;  (** The expression of the macro's code that it splices. *)
}

and segment = Text of string | Splice of expr * string option
and arg = { inout : bool; value : expr }
and field_init = { field : name; value : expr }

and arm = {
  pattern : pattern;
  guard : expr option;
  because : string node option;
  body : expr;
}

and closure_param = { mode : mode; pattern : pattern; annotation : ty option }
(** A parameter marked [inout] is a binding. *)

and iterable = Iter of expr | Range of expr * expr * Ast.range_end
and block = stmt list
and stmt = stmt_desc node

and stmt_desc =
  | Let of binding
  | Var of binding
  | Assign of Ast.binary option * expr * expr
  | Assert of expr
  | Yield of expr  (** In a projection's body. *)
  | Expr of expr

and binding = { pattern : pattern; annotation : ty option; value : expr }

(** {1 Declarations} *)

type generic = Type_param of type_param | Row_param of var

type param =
  | Self_param of mode * var * ty option
      (** A receiver, with the type it writes in a constructor trait and its
          impls. *)
  | Param of mode * var * ty * bool
      (** A parameter, and whether it is [escaping]. *)

type fn_body =
  | Body of block * loc  (** A written body, and its closing brace. *)
  | Body_hole of loc  (** [= ?], at the [?]. *)

type capability = Ast.capability

type limit = Ast.limit =
  | Panic
  | Overflow
  | Alloc
  | Div
  | Copy
  | Capability of capability
  | Locks
  | Unsafe

type fn_decl = {
  name : name;
  generics : generic list;
  params : param list;
  ret : ty option;
  projection : bool;
      (** Whether it is a projection, whose result is written [inout T]. *)
  row : row;
  limits : limit node list;
      (** The limits of its [without] clause, each once: a limit named twice
          holds only as an error. *)
  body : fn_body option;  (** [None] for a trait method without a default. *)
  where_bounds : (ty * bound * loc) list;
      (** The bounds of its [where] clause on types other than its own type
          parameters, each at its member type: one that a bound's argument
          fixes, which must meet it, and one of its inherent impl's parameter,
          which its body may assume and its calls must meet (traits.where). *)
}

type variant_decl = { name : name; payload : ty list }
(** Payload names are documentation only, so they are gone. *)

type type_def =
  | Record of field_decl list
  | Variants of variant_decl list
  | Native
      (** A native type of the standard library, which has no written
          representation. *)

type type_decl = { name : name; params : var list; def : type_def }
(** A type, whose parameters are its type parameters and value parameters, in
    order. *)

type const_decl = { name : name; ty : ty; value : expr option }
(** A constant. Only a trait's leaves out its value. *)

type doc_line =
  | Doc_text of string
  | Doc_example of expr
  | Doc_property of string * expr
      (** Its text, which seeds its cases, and its closure (tests.prop-lines and
          tests.seeds). *)

type decl = {
  pub : bool;
  exported : bool;  (** Whether it is written [pub extern fn] with a body. *)
  foreign : bool;  (** Written [extern fn] with no body. *)
  doc : doc_line list;
  kind : decl_kind;
  unknown : bool;
      (** Whether a part with a syntax error declares only its name, as
          errors.declarations-with-errors and errors.error-type says: every use
          of the name has the error type. *)
}

and decl_kind =
  | Fn of fn_decl
  | Type of type_decl
  | Trait of trait_decl
  | Const of const_decl
  | Test of string * block
  | Effect of effect_decl  (** An effect. *)

and effect_decl = {
  name : name;
  params : var list;
  ops : operation list;  (** Each named once. *)
}

and operation = {
  op : name;
  params : (mode * var * ty) list;
  ret : ty option;
  row : row;  (** Its own row, which holds no row variable. *)
}

and trait_decl = {
  name : name;
  params : var list;  (** Its trait parameters. *)
  arity : int;
      (** For a constructor trait, the number of arguments its [Self] takes, and
          0 for a trait over types. *)
  members : decl node list;
}

type impl_decl = {
  generics : type_param list;
      (** Its type parameters, those that member types imply last. *)
  trait_ : bound option;  (** [Some] for [impl Trait<…> for T]. *)
  where_bounds : (ty * bound * loc) list;
      (** The bounds of its [where] clause on member types that a bound's
          argument fixes, which must meet them (traits.where). *)
  self_ty : ty;
  members : decl node list;
}

type macro = {
  macro_name : name;
  names : (item * loc) list;
      (** The functions its templates name, and where: its package's to name, as
          a call into it would be (macros.expansion-effects). *)
}
(** A pattern macro, which is no declaration of the resolved program: its uses
    are expanded where they are written (macros.matching). *)

(** The tiers that the Reference gives features of. *)
type tier = Core | Advanced | Meta | Systems

type module_ = {
  name : string;
      (** The module's dotted name. A module whose name is invalid
          (program.module-names) is named by its file instead, which no name in
          a program can refer to. *)
  file : string;  (** The path that reports name the module's file by. *)
  std : bool;  (** Whether the module is part of the standard library. *)
  tier : tier;
      (** The first tier that allows every feature the module uses, which it
          infers (program.module-tier): [Meta] for a module that declares a
          value parameter (generics.meta-tier) or writes [comptime]
          (meta.staging-tier), [Advanced] for a module that names [View] or
          [Iter] of [std.view] (views.std-view), declares a projection
          (projections.declaring-projection), or declares, implements or bounds
          with a trait that has parameters, functions without [self], constants
          or a constructor [Self], or writes a member type or a [where] clause
          (traits.advanced-tier), writes an anonymous record type, literal or
          pattern, a record bound, an open record type or an update of a record
          that isn't named (records.advanced-tier), declares a pack
          (variadics.advanced-tier) or declares a macro (macros.advanced-tier),
          and [Core] for every other. What a macro's expansion writes leaves the
          module that uses it in its tier. A module that only calls a projection
          is advanced too, which type checking knows and nothing the reference
          interpreter reports depends on. *)
  limits : limit node list;
      (** The limits of its header's [without] clause, each once. *)
  imports : string list;
      (** The modules that [use] declarations import, whose traits are visible
          to method calls. *)
  decls : decl node list;
      (** In source order. Of two declarations with the same name, the first is
          the one that names refer to. *)
  impls : impl_decl node list;
  macros : macro list;  (** The macros it declares, in source order. *)
  procs : name list;
      (** The procedural macros it declares, in source order, each among [decls]
          as a function of its signature (macros.procedural-declarations and
          macros.procedural-bodies). *)
  unresolved : loc list;
      (** The bodies in which name resolution reported an error, so that only
          type checking runs on them (errors.phases). Each is known by the
          position of the name of its function or constant, of its test's [test]
          keyword, or of its doc example. *)
  held : (loc * string * Diagnostic.t) list;
      (** The E0211 that name resolution holds back for type checking, each with
          its body and its name: those of names that a pattern of the body also
          writes without a module, whose failure only type checking finds, so
          that the body reports one E0211 for the name, where it fails first
          (errors.error-type). *)
}

type program = module_ list
(** Every module of the program and of the standard library, sorted by name. *)
