(** The syntax tree that the parser produces, before any desugaring.

    It follows [reference/03-syntax.md] production by production. Field punning
    is already expanded, so [Order { qty }] holds the field [qty] with the value
    [qty], and parentheses that only group leave no trace (syntax.tree-form). *)

type loc = { line : int; col : int }
(** The position of a node's first token. *)

type 'a node = { desc : 'a; loc : loc }
type name = string node

type path = name list
(** A path of one or more names joined by [.], such as [std.fs] or
    [shapes.Circle]. *)

type mode = Let | Inout

(** {1 Macros} *)

(** A token that stands for itself in a macro's pattern or template, or in a
    use's groups: any token of lexical.tokens but a bracket and [$]. *)
type atom =
  | A_lower of string  (** A [lower] identifier. *)
  | A_upper of string  (** An [Upper] identifier. *)
  | A_word of string  (** A keyword, a reserved word or [_]. *)
  | A_int of string
  | A_float of string
  | A_string of string  (** A string literal, with its escapes resolved. *)
  | A_string_head of string
  | A_string_mid of string
  | A_string_tail of string
  | A_format of string
  | A_punct of string  (** An operator or a punctuation mark, as written. *)
  | A_sep  (** A separator: a written [;] or an inserted one. *)

type delim = Paren | Bracket | Brace

type tree = tree_desc node
(** A token tree of a macro's pattern or template, or of a use. *)

and tree_desc =
  | Token of atom
  | Group of delim * tree list * loc
      (** A group, with the position of its closing bracket. *)
  | Fragment of name * name option
      (** [$name: kind] in a pattern, or [$name] in a template, at its [$]. *)
  | Repeat of tree list * string option * string
      (** [$( … ) sep op], at its [$]: its contents, its separator, [","] or
          [";"], and its operator, ["*"] or ["+"]. *)

(** {1 Operators and limits} *)

(** A capability below [io], in the order of facts.capabilities. *)
type capability = Fs | Net | Clock | Env | Console | Rand | Spawn | Exec

(** A limit of a [without] clause (program.header-limits; facts.spelling;
    facts.without). It is declared before {!binary}, whose [Div] is the one a
    bare [Div] names. *)
type limit =
  | Panic
  | Overflow  (** An operation that can overflow. *)
  | Alloc
  | Div
  | Copy
  | Capability of capability
  | Locks  (** Holding a shared value in a [when]. *)
  | Unsafe  (** Holding an [unsafe] block. *)

type unary = Neg | Not

type binary =
  | Add
  | Sub
  | Mul
  | Div
  | Rem
  | Add_wrap
  | Sub_wrap
  | Mul_wrap
  | Eq
  | Ne
  | Lt
  | Le
  | Gt
  | Ge
  | And
  | Or
  | Bit_and
  | Bit_or
  | Bit_xor
  | Shl
  | Shr

(** {1 Types} *)

type ty = ty_desc node

and ty_desc =
  | Ty_named of path * ty list
      (** [i64], [Order], [m.T], [Self] or [List<Order>]. An argument may be a
          value: a name or a path among its arguments, as in [Mod<PRIME>] and
          [Array<T, n>], is read as a type or a value after parsing
          (generics.value-argument-names). *)
  | Ty_int of string
      (** An integer literal given as a value argument, as written without [_],
          after its [-] if one is written, as in [Array<T, -1>]
          (generics.value-arguments). *)
  | Ty_bool of bool  (** [true] or [false] given as a value argument. *)
  | Ty_tuple of ty list  (** [()] is the empty tuple. *)
  | Ty_record of field_decl list * bool
      (** [{ f: T, g: U }], an anonymous record type, and whether it ends with
          [..], which makes it open (records.anonymous-types and
          records.open-parameter-types). *)
  | Ty_spread of ty
      (** [..T], among a tuple type's elements or a function type's parameters.
      *)
  | Ty_fn of type_param list * (mode * ty) list * ty option * row
      (** [fn<T: B>(A, inout B) -> C / row]: type parameters, which only a
          polymorphic function type has (polymorphism.function-types),
          parameters, return type and row. A spread parameter is [Ty_spread]. *)
  | Ty_handler of effect_ref * ty option * row
      (** [handler E -> R / row], a handler's type: its effect, the [R] of one
          that takes control, and its row (handlers.handler-types). *)
  | Ty_macro of path * tree
      (** A use of a procedural macro whose result is a type: its path and its
          group, unexpanded. *)
  | Ty_splice of expr
      (** In a quote, [$t] or [$(e)] where a type stands, at its [$]: the
          expression of the macro's code whose value it splices
          (macros.splices). *)

(** The effect of a handler: a named effect with its type arguments, or [async]
    at its keyword. *)
and effect_ref = Effect_named of path * ty list | Effect_async of loc

and row = row_elem list
(** An effect row, empty when none is written. *)

and row_elem =
  | Row_io of loc
  | Row_raise of loc * ty  (** [raise<T>], at its [raise]. *)
  | Row_var of name  (** A row variable, such as [e]. *)
  | Row_effect of path * ty list
      (** An effect with its type arguments, such as [State<i64>]. *)
  | Row_async of loc  (** [async]. *)

and field_decl = { field : name; ty : ty }

(** A bound. *)
and bound =
  | Trait_bound of { trait : path; args : ty list }
      (** A trait with all of its arguments, or with none. *)
  | Record_bound of ty
      (** The fields a record needs, written as a record type, [{ f: T, .. }].
      *)

and type_param = {
  name : name;
  bounds : bound list;
  pack : bool;
  value : ty option;
      (** For a value parameter, [n: i64], its type (generics.value-parameters):
          its name is lowercase, and it has no bounds and is no pack. *)
}
(** A type parameter, which is a pack when it is written [..T], or a value
    parameter. *)

(** {1 Patterns} *)

and pattern = pattern_desc node

and pattern_desc =
  | P_wild
  | P_bind of string
  | P_int of string  (** An integer literal with its sign, such as [-5]. *)
  | P_str of string
  | P_bool of bool
  | P_tuple of pattern list  (** [()] is the empty tuple. *)
  | P_path of path  (** A constant, or a variant without a payload. *)
  | P_variant of path * pattern list
  | P_record of path option * field_pattern list * bool
      (** The record type, [None] for an anonymous record's pattern
          (records.anonymous-patterns), the fields, and whether [..] ends the
          list. *)
  | P_list of pattern list * list_rest
  | P_or of pattern list  (** Two or more alternatives. *)
  | P_macro of path * tree
      (** A macro's use, its path and its group, unexpanded. *)
  | P_splice of expr
      (** In a quote, [$p] or [$(e)] where a pattern stands, at its [$]: the
          expression of the macro's code whose value it splices
          (macros.splices). *)
  | P_spliced_record of path option * spliced_field_pattern list * bool
      (** A record's pattern in a quote, as [P_record], of which a field's name
          is spliced. *)

and field_pattern = { field : name; pattern : pattern }

(** A field of a record's pattern in a quote: a field, or [$f: p], whose splice,
    a [Q_splice], names the field (macros.splices). *)
and spliced_field_pattern =
  | Field_pattern of field_pattern
  | Spliced_field_pattern of expr * pattern

and list_rest = Exact | Rest | Rest_bind of name

(** {1 Expressions and statements} *)

and expr = expr_desc node

and expr_desc =
  | Int of string  (** An integer literal as written, without [_]. *)
  | Float of string  (** A float literal as written, without [_]. *)
  | Str of string
  | Interpolated of segment list
  | Bool of bool
  | Name of string  (** An identifier. *)
  | Self_value  (** [self]. *)
  | Self_type  (** [Self], as in [Self.new()]. *)
  | Key_root
      (** The [.] that starts a key path. The rest of the path is built on it:
          [.name.len()] is a call of the field [len] of the field [name] of a
          [Key_root]. *)
  | Hole
  | Tuple of expr list  (** [()] is the empty tuple. *)
  | List of expr list
  | Field of expr * name  (** [e.x], [e.0] and [m.X] alike. *)
  | Call of expr * arg list  (** A method call is a call of a field. *)
  | Index of expr * expr
  | Struct of path * expr option * field_init list
      (** A struct literal, or an update with its base, [Name { ..base, f: e }].
      *)
  | Record_literal of expr option * field_init list
      (** [{ f: e }], an anonymous record literal, or [{ ..base, f: e }], an
          update. *)
  | Spread of expr
      (** [..e], among a tuple's or a list's elements or a call's arguments. *)
  | Unary of unary * expr
  | Binary of binary * expr * expr
  | Else of expr * expr
  | Try of expr * arm list option  (** The operand, and the [catch] arms. *)
  | Raise of expr
  | Return of expr option
  | Break
  | Continue
  | Closure of closure_param list * expr
  | Block of block
  | If of expr * block * expr option
      (** The [else] branch is a [Block], an [If] or an [If_let]. *)
  | If_let of pattern * expr * block * expr option
      (** [if let P = e { … }], whose [else] is as an [If]'s. *)
  | Match of expr * arm list
  | Loop of block
  | While of expr * block
  | For of pattern * iterable * block
  | Macro_use of path * tree list
      (** A macro's use: its path, its group and its trailing block, if any,
          unexpanded. *)
  | Handler of effect_ref * ty option * fn_decl list
      (** [handler E -> R { fn op(…) { … } … }]: its effect, the [R] of one that
          takes control, and its operations (handlers.handler-literals). *)
  | With of expr list * block  (** [with h₁, h₂ { … }]. *)
  | Resume of expr option  (** [resume(v)] or [resume()]. *)
  | When of name list * block
      (** [when a, b { … }], which holds the values of shared handles. *)
  | Comptime of expr
      (** A staging annotation: [comptime] before an [If], an [If_let], a
          [Match] or a [For], which it holds. *)
  | Unsafe of string node * block
      (** [unsafe because "reason" { … }], at its [unsafe]: its reason, at the
          string, and its block. *)
  | Bound_test of name * bound list
      (** [T: B + …], a bound test, which is only the whole condition of an
          [If]. *)
  | Quote of quote  (** A quote. *)
  | Q_splice of expr
      (** In a quote, [$x] or [$(e)], at its [$]: the expression of the macro's
          code whose value it splices, [x] for [$x] (macros.splices). *)
  | Q_spread of expr
      (** In a quote, [$..x] or [$..(e)], at its [$], among the elements of a
          tuple or a list or a call's arguments, or a record's fields. *)
  | Q_member of expr * expr
      (** [e.$f] in a quote: the receiver, and the [Q_splice] that names the
          member. *)
  | Q_record of expr option * spliced_field list
      (** An anonymous record literal in a quote, as [Record_literal], with a
          field that a splice names or a spread. *)
  | Q_struct of path * expr option * spliced_field list
      (** A struct literal in a quote, as [Struct], with a field that a splice
          names or a spread. *)

and segment =
  | Text of string
  | Splice of expr * string option
      (** A part of an interpolated string: text, or an expression with its
          format spec. Text parts are never empty. *)

and arg = { inout : bool; value : expr }
and field_init = { field : name; value : expr }

(** A field of a record literal in a quote: a field, [$n: e], whose [Q_splice]
    names it, or a [Q_spread] of fields (macros.splices and macros.spreads). *)
and spliced_field =
  | Field_init of field_init
  | Spliced_field of expr * expr
  | Spread_fields of expr

and quote = {
  form : quote_form;
  tokens : tree list;
      (** Its contents as tokens, without the braces around them, which the
          macro's run writes out, filling its splices (macros.outside-run). *)
}

(** What a quote holds: [quote { … }]'s statements, [quote type { … }]'s type,
    [quote pattern { … }]'s pattern, or [quote field { … }]'s field. *)
and quote_form =
  | Quote_block of block
  | Quote_type of ty
  | Quote_pattern of pattern
  | Quote_field of spliced_field

and arm = {
  pattern : pattern;
  guard : expr option;
  because : string node option;
  body : expr;
}

and closure_param = { mode : mode; pattern : pattern; annotation : ty option }
(** A parameter marked [inout] is a binding. *)

and iterable = Iter of expr | Range of expr * expr * range_end
and range_end = Exclusive | Inclusive
and block = stmt list
and stmt = stmt_desc node

and stmt_desc =
  | Let of binding
  | Var of binding
  | Assign of binary option * expr * expr
      (** [p = e] has no operator, and [p += e] has [Add]. *)
  | Assert of expr
  | Yield of expr  (** [yield e], in a projection's body. *)
  | Expr of expr

and binding = { pattern : pattern; annotation : ty option; value : expr }

(** {1 Declarations} *)

and fn_decl = {
  name : name;
  generics : generic list;
  params : param list;
  ret : ty option;
  projection : bool;
      (** Whether its result is written [inout T]: a projection, whose body
          yields a place of type [T]. *)
  row : row;
  where_ : where_ option;  (** Its [where] clause. *)
  without : without option;  (** Its limits. *)
  body : fn_body option;  (** [None] for a trait method without a default. *)
}
(** A function's declaration, which a handler literal also holds. *)

and generic =
  | Type_param of type_param
  | Row_param of name
      (** A generic: a type or value parameter, or a row variable. *)

and where_bound = { bounded : path; bounds : bound list }
(** A bound of a [where] clause, on a member type such as [C.Item]. *)

and where_ = where_bound list node
(** A [where] clause, at its [where] keyword. *)

and param =
  | Self_param of mode * loc * ty option
      (** A receiver, with the type it writes, as [self: Self<A>]. *)
  | Param of mode * name * ty * bool
      (** A parameter, and whether it is [escaping]. *)

and fn_body =
  | Body of block * loc
      (** A written body, and the position of its closing brace, where a
          projection that reaches its end without a [yield] is reported
          (projections.once-on-every-path). *)
  | Body_hole of loc  (** [= ?], at the [?]. *)

and without = limit node list node
(** A [without] clause: its limits, in order, at the [without] keyword. *)

type variant_decl = { name : name; payload : (name option * ty) list }

type type_def =
  | Record of field_decl list
  | Variants of variant_decl list
  | Native of loc
      (** [= ?], at its [?]: a native type, which only the standard library
          declares. *)

type type_decl = { name : name; params : type_param list; def : type_def }
(** A type, whose parameters have no bounds, and of which one may be a pack
    (variadics.packs), and others value parameters (generics.value-parameters).
*)

type const_decl = { name : name; ty : ty; value : expr option }
(** A constant. Only a trait's leaves out its value. *)

type macro_arm = {
  pattern : tree;  (** Its group of matchers. *)
  block : (name * name) option;  (** Its trailing block's name and kind. *)
  template : tree list;
}

type syntax_decl = { name : name; arms : macro_arm list }
(** A pattern macro. *)

type doc_line =
  | Doc_text of string
  | Doc_example of expr
  | Doc_property of string * expr
      (** Its text, which seeds its cases, and its closure (tests.prop-lines and
          tests.seeds). *)

type operation = {
  op_doc : doc_line list;
  op_name : name;
  op_params : param list;
  op_ret : ty option;
  op_row : row;
}
(** An operation of an effect: a function's head, without generics, an [inout]
    result or a body. *)

and effect_decl = { name : name; params : name list; ops : operation list }
(** An effect, with its type parameters and operations. *)

type decl = {
  pub : bool;
  exported : bool;
      (** Whether it is a function written [pub extern fn] with a body, which a
          C program linked with the program's library calls
          (c.exported-functions). *)
  foreign : bool;
      (** Whether it is a function written [extern fn] with no body, which C
          gives. *)
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
  | Syntax of syntax_decl
  | Effect of effect_decl  (** An effect. *)
  | Macro of fn_decl
      (** A procedural macro, written as a function whose result is always
          written. *)

and trait_decl = {
  name : name;
  params : type_param list;  (** Its trait parameters, which have no bounds. *)
  members : decl node list;
}

type impl_decl = {
  generics : type_param list;
  trait_ : bound option;  (** [Some] for [impl Trait<…> for T]. *)
  self_ty : ty;
  where_ : where_ option;  (** Its [where] clause. *)
  members : decl node list;
}

type item = item_desc node

and item_desc =
  | Use of path
  | Meta_use of path  (** [meta use a.b]. *)
  | Decl of decl
  | Impl of impl_decl

type header = {
  path : path;
  withouts : without list;  (** Its [without] clauses, in order. *)
}

type module_ = { header : header node option; items : item list }
