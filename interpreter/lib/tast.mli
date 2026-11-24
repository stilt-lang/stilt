(** The program after type checking, which the evaluator runs.

    Every expression carries its type, every literal its numeric type, and every
    call its target and type arguments. Trait methods are called through the
    type that implements them, so the evaluator finds each impl from types, as
    dictionary passing would. *)

type ty = Types.ty
type row = Types.row

(** What a signature pairs a row variable with: an error type
    (effects.paired-row-variables), or an effect with its arguments
    (handlers.with-pairing). *)
type label = Raise_label of ty | Effect_label of Hir.item * ty list

(** A function that a program can call by name. *)
type callee =
  | Function of Hir.item  (** A function of a module. *)
  | Member of Hir.item * string
      (** A function of an inherent impl of a type constructor. *)
  | Trait_method of Hir.item * string * ty
      (** A method of a trait, of the impl for a type. *)
  | Operation of Hir.item * string
      (** An operation of an effect, which a call performs on the nearest
          handler of its effect (handlers.performing-operation). Its type
          arguments are the effect's. *)

type expr = { desc : expr_desc; ty : ty; loc : Ast.loc }

and expr_desc =
  | Int of string  (** A literal as written, of the numeric type [ty]. *)
  | Float of string
  | Str of string
  | Interpolated of segment list
  | Bool of bool
  | Local of Hir.var
  | Value_param of Hir.var
      (** A value parameter, whose value the type arguments of the body that
          reads it give (generics.value-parameters-in-body). *)
  | Constant of Hir.item
  | Member_constant of Hir.item * string * ty list
      (** [Type.NAME], with the type's arguments. *)
  | Trait_constant of Hir.item * string * ty
      (** A constant of a trait, of the impl for a type, or the trait's default
          for it (traits.trait-constants). *)
  | Callee of callee * ty list
      (** A function as a value, with its type arguments: the impl's, then its
          own. *)
  | Constructor of Hir.item * ty list
      (** A variant with a payload, as a value. *)
  | Generalize of Hir.var list * expr
      (** A generic function or a closure given where a polymorphic function
          type is expected, checked with these rigid types for its type
          parameters: a value whose every use gives them types
          (polymorphism.rigid-types). *)
  | Instantiate of expr * ty list
      (** A value of a polymorphic function type at one use, with the types its
          type parameters take there (polymorphism.instantiation). *)
  | Construct of Hir.item * ty list * expr list  (** A variant applied. *)
  | Record of Hir.item * ty list * (string * expr) list
      (** A record literal, with its fields in the order they are written. An
          anonymous record's names {!Types.anonymous}
          (records.anonymous-literals). *)
  | Update of expr * (string * expr) list
      (** [{ ..base, f: e }]: a record of the base's type, with the fields
          written, in the order they are written, in place of the base's
          (records.update). *)
  | Spread of spread
      (** [..e], an element of a tuple or a list, or a call's argument, which
          stands for one value for each element of its pack
          (variadics.spread-expressions). Its type is the spread
          [Types.Spread (pack, body.ty)]. *)
  | Tuple of expr list
  | List of expr list
  | Field of expr * string
  | Tuple_field of expr * int
  | Call of callee * ty list * arg list * row
      (** A call by name, with the row it performs. A method's receiver is its
          first argument. *)
  | Project of callee * ty list * arg list * row
      (** The call of a projection, which is a place of its result type
          (projections.call-is-place). *)
  | Call_value of expr * arg list
  | Index of expr * expr  (** Of a list or a map, as the first's type says. *)
  | Unary of Ast.unary * expr
  | Binary of Ast.binary * expr * expr
  | Else of expr * expr
  | Try of expr * catch option
  | Raise of expr
  | Return of expr option
  | Break
  | Continue
  | Closure of pattern list * Hir.ty list * expr
      (** Its parameters, the types written for them, which phase 2 reads for
          views (views.viewable-types and views.view-types), and its body. *)
  | Block of block
  | If of expr * block * expr option
  | If_let of pattern * expr * block * expr option
  | Match of expr * arm list
  | Loop of block
  | While of expr * block
  | For of pattern * iterable * block
  | Hole
  | Handler of handler
      (** A handler literal (handlers.handler-literals), whose type is a
          [Types.Handler]. *)
  | With of expr * Hir.item * ty list * block
      (** [with h { … }]: the handler, the effect it handles with its arguments,
          and the block (handlers.with). A [with] of several handlers is one
          [With] in another. *)
  | Resume of expr option
      (** [resume(v)], in an operation's body of a handler that takes control
          (handlers.resuming). *)
  | When of (expr * Hir.var) list * block
      (** [when a, b { … }]: each handle, of type [Shared<T>], with the binding
          that stands in the block for the place of its value, of type [T]
          (shared.when). *)
  | Comptime of expr
      (** A staging annotation of an [If], an [If_let], a [Match] or a [For],
          which means what the form means, and has its type
          (meta.staging-annotations and meta.erasure). *)
  | Reflect of reflect
      (** Reflection on a type (meta.shape-and-name and meta.bound-tests): its
          shape, its name or a bound test. *)
  | Quote of quote
      (** A quote, whose run writes its tokens out with its splices filled
          (macros.quote and macros.splices). Its type is [meta.Expr],
          [meta.Type], [meta.Pattern] or [meta.FieldInit]. *)
  | Error
      (** An expression with an error, which only bodies that [run] replaces
          hold (program.errors-in-bodies). *)

and quote = {
  home : string;  (** The module where it is written. *)
  form : Hir.code;
  tokens : Ast.tree list;  (** Its contents, as written. *)
  splices : splice list;  (** In the order of their [$]. *)
  names : (Hir.item * Ast.loc) list;
      (** The functions its contents name (macros.expansion-effects). *)
}

and splice = {
  place : Hir.place;
  spread : bool;
  at : Ast.loc;  (** Its [$]. *)
  value : expr;
}

and reflect =
  | Shape_of of ty  (** [T.shape()], a [meta.Shape<T>] (meta.shape-and-name). *)
  | Name_of of ty
      (** [T.name()], as a diagnostic writes the type (meta.shape-and-name). *)
  | Implements of ty * Types.bound list
      (** A bound test, true when the type has an impl of each bound, whose own
          bounds hold (meta.bound-tests). *)

and handler = {
  heffect : Hir.item;
  control : bool;  (** Whether it takes control, written [-> R]. *)
  ops : (string * expr) list;
      (** Its operations, each a closure literal of the operation's type, whose
          body is the operation's: its bodies are code of the function that
          writes it, as a closure literal's are
          (handlers.implicit-effects-and-capabilities). *)
}

and spread = {
  pack : ty;  (** The pack of the tuples it maps, a type parameter. *)
  tuples : Hir.var list;
      (** The pack tuples it names, which stand for their elements in [body]. *)
  body : expr;
      (** Evaluated once for each element, with each pack tuple its element and
          the pack that element's type. *)
}

and segment = Text of string | Splice of expr * string option

and arg = {
  mode : Ast.mode;  (** Its parameter's, or for a receiver, its [self]'s. *)
  value : expr;
}

and catch = {
  error : ty;  (** The type [E] that the arms handle (effects.catch). *)
  arms : arm list;
}

and arm = {
  pattern : pattern;
  guard : expr option;
  because : bool;
      (** Whether the arm gives a reason (effects.catch-alls-need-reason). *)
  body : expr;
}

and iterable = Iter of expr | Range of expr * expr * Ast.range_end
and block = stmt list
and stmt = { stmt : stmt_desc; at : Ast.loc }

and stmt_desc =
  | Let of binding
  | Var of binding
  | Assign of Ast.binary option * expr * expr
  | Assert of expr
  | Yield of expr
      (** [yield e]: a place, or an expression of a view type that a temporary
          holds (projections.yield). *)
  | Expr of expr

and binding = {
  pattern : pattern;
  written : Hir.ty option;
      (** The type written for it, which phase 2 reads for views
          (views.viewable-types and views.view-types). *)
  value : expr;
  otherwise : expr option;
      (** The [else] branch of a let-else (patterns.let-else). *)
}

and pattern = { pat : pattern_desc; pty : ty; ploc : Ast.loc }

and pattern_desc =
  | P_wild
  | P_bind of Hir.var
  | P_int of string
  | P_str of string
  | P_bool of bool
  | P_tuple of pattern list
  | P_const of expr  (** A constant, which matches values equal to it. *)
  | P_variant of Hir.item * pattern list
  | P_record of (string * pattern) list
  | P_list of pattern list * list_rest
  | P_or of pattern list
  | P_error

and list_rest = Exact | Rest | Rest_bind of Hir.var

(** {1 Programs} *)

(** What an item of the program is defined by. *)
type 'a definition =
  | Native
      (** A native item of the standard library, or a foreign function, which C
          gives (c.foreign-functions). *)
  | Code of 'a
  | Broken
      (** Code with an error, which the later phases of checking skip
          (errors.phases). [run] replaces it with a [check-error] panic
          (program.check-error-report). *)

type fn_def = {
  home : string;  (** The module that defines it. *)
  at : Ast.loc;  (** Its name, where a [check-error] panic is reported. *)
  params : (Ast.mode * Hir.var) list;
      (** Its parameters, its receiver's first for a method. *)
  type_params : Hir.var list;
      (** Its type parameters, its impl block's first for a method, as its
          signature gives them. *)
  through : Hir.var list;
      (** Its non-escaping parameters, which pass their arguments' effects
          through (effects.non-escaping-parameters). *)
  pairs : (Hir.var * label) list;
      (** The row variables that its signature pairs with an error type or an
          effect, with that label (effects.paired-row-variables;
          handlers.with-pairing). *)
  passed : (Ast.loc * row * label) list;
      (** For each use of a function whose signature pairs a row variable with
          an error type, the row and the error type that the use gives them
          (effects.passing-to-paired-variables). *)
  limits : Ast.limit list;
      (** The limits of its own [without] clause (declarations.limits). Its
          module's limits are its module's. *)
  yields : Ast.loc option;
      (** For a projection, the closing brace of its body, where a path that
          ends without a [yield] is reported (projections.declaring-projection
          and projections.once-on-every-path). *)
  unsafe_blocks : Ast.loc list;
      (** The [unsafe] blocks of its own code, its closures' included, in order
          (c.unsafe-and-foreign). *)
  body : block definition;
}

type test = {
  name : string;
  file : string;
  loc : Ast.loc;  (** The position of its [test] keyword. *)
  block : block definition;
}

type example = {
  file : string;
  loc : Ast.loc;  (** The position of the example, on its [/// ex:] line. *)
  claim : expr definition;  (** The expression that must be [true]. *)
}

type property = {
  file : string;
  loc : Ast.loc;  (** The position of the property, on its [/// prop:] line. *)
  text : string;
      (** Its text, which seeds its cases (tests.prop-lines and tests.seeds). *)
  closure : expr definition;
      (** A closure, whose parameters' types are generated
          (tests.property-form). *)
}

type program = {
  functions : (Hir.item * fn_def) list;
  members : ((Hir.item * string) * fn_def) list;
      (** The functions of inherent impls, by type constructor and name. *)
  impl_methods : ((Hir.item * Hir.item * string) * fn_def) list;
      (** The methods of trait impls, by trait, type constructor and name. *)
  default_methods : ((Hir.item * string) * fn_def) list;
      (** The default methods of traits, by trait and name. *)
  default_constants : ((Hir.item * string) * expr definition) list;
      (** The default values of traits' constants, by trait and name
          (traits.trait-constants), in terms of the trait's [Self]. *)
  constants : (Hir.item * expr definition) list;
  member_constants : ((Hir.item * string) * expr definition) list;
      (** The constants of inherent impls, by type constructor and name. *)
  impl_constants : ((Hir.item * Hir.item * string) * expr definition) list;
      (** The constants of trait impls, by trait, type constructor and name, so
          that two traits may give a type constants of one name
          (traits.shared-member-names). *)
  tests : test list;
  examples : example list;
  properties : property list;
}
