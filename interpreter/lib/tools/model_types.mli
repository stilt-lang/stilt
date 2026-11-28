(** The types of a program as the Lean model's calculus writes them, and what an
    export has met: the record and variant types it names, and the functions it
    reaches. A form the calculus lacks raises {!Outside}. *)

exception Outside of string
(** The program uses something the model's calculus lacks, which it names. *)

val outside : ('a, unit, string, 'b) format4 -> 'a
(** Raises {!Outside} with the message. *)

type instance = {
  key : string;
  item : Hir.item;
  args : Types.ty list;
  generic : bool;
}
(** A record or variant type that the calculus declares, named [key]: a generic
    type once, at its own type parameters, which its uses give arguments, when
    [generic], and otherwise a type at one list of arguments, as a type of its
    own. *)

type target =
  | Function of Hir.item
  | Member of Hir.item * string
  | Impl of Hir.item * Hir.item * string
  | Default of Hir.item * Hir.item * string
      (** A function, a function of a type's inherent impls, a method of the
          impl of a trait for a type constructor that the program writes, or the
          default of a trait's method, for a type constructor whose impl leaves
          the method out (traits.impl-members). *)

type fn_instance = {
  fkey : string;  (** Its name in the calculus. *)
  target : target;
  types_of : (Hir.var * Types.ty) list;  (** Its type parameters' arguments. *)
  rows_of : (Hir.var * Types.row) list;  (** Its row parameters' rows. *)
}
(** A function at one instantiation, which the calculus declares as a function
    of its own. *)

type access = {
  res : string;  (** The variable that keeps the access's value. *)
  result : Types.ty;  (** The access's value's type. *)
  k : Tast.expr;  (** The parameter that holds the access. *)
  extras : Tast.expr list;
      (** The parameters of the places that the access threads, [inout]. *)
}
(** A projection's body written for one access
    (projections.when-projection-runs). *)

type writable = {
  src : string;
      (** The variable that holds its source: an [inout] parameter of the
          closure that its scope is, or of the function whose parameter it is.
      *)
  start : string;  (** The variable that holds its part's start. *)
  stop : string;  (** The variable that holds its part's end. *)
  part : Types.ty;  (** The viewed type, a list's. *)
}
(** What a writable binding stands for (projections.writable-bindings). *)

type cx = {
  env : Env.t;
  program : Tast.program;
  mutable types : instance list;  (** The declared types met, newest first. *)
  mutable fns : fn_instance list;  (** The functions reached, newest first. *)
  mutable reads_input : bool;
      (** Whether the program reads stdin, which the export then gives it. *)
  mutable effects : (string * Model_json.t) list;
      (** The effects met, each at its arguments, with its declaration. *)
  mutable handlers : (string * Model_json.t) list;
      (** The handler types met, each with the record that stands for it. *)
  mutable lazy_met : bool;  (** Whether the program has a lazy value. *)
  mutable when_met : bool;  (** Whether the program has a [when]. *)
  mutable raises : Types.ty option;
      (** The error type of the code being exported. *)
  mutable helpers : (string * Model_json.t) list;
      (** The functions the export writes of its own, each with its declaration:
          [par.fold]'s tree at each type. *)
  mutable projections : (Hir.item * (Env.fn_sig * Tast.fn_def * access)) list;
      (** The projections written for an access, each a function of its own. *)
  mutable yielding : access option;
      (** The access of the projection whose body is being exported. *)
  mutable writable : (string * writable) list;
      (** The bindings of a view type that write their sources, [var]s and
          [inout] parameters (projections.writable-bindings), by their names. *)
  mutable consts : (string * Tast.expr) list;
      (** The constants met in patterns, newest first, each with its value
          (patterns.constants). *)
  mutable allowed : Types.row;
      (** The row the code being exported may perform: its function's or
          closure's, with the effects of the [with]s around it and the error of
          a [catch] around it. *)
}

val item_name : Hir.item -> string

val param_parts :
  cx -> Ast.mode * string * Types.ty -> (Ast.mode * string * Model_json.t) list
(** The parameters the calculus writes for a parameter of a mode, a name and a
    type: itself, or for an [inout] one of a view type, which is writable, its
    source's place, [inout], and its part's start and end
    (projections.writable-bindings). *)

val param_decls : cx -> Ast.mode * string * Types.ty -> Model_json.t list
(** The declarations of {!param_parts}. *)

val viewed : Types.ty -> Types.ty option
(** [Some t] for a view type [View<t>]. *)

val writable_of : cx -> Hir.var -> writable option
(** The writable binding a variable is, if it is one. *)

val bind_writable : cx -> Hir.var -> writable -> unit
(** Records a writable binding by what it stands for. *)

val writes : cx -> Ast.mode -> Hir.var -> Types.ty -> unit
(** Records the binding as writable when it is an [inout] one of a view type,
    which stands for the three parameters of {!param_parts}. *)

val aliases : (int * Hir.var) list ref
(** The bindings of a [when] written as another of its names, when their handles
    reach one value (shared.names-that-may-be-one-place). *)

val var_name : Hir.var -> string

val norm : Types.ty -> Types.ty
(** The type a solved variable stands for. *)

val array_item : Hir.item
(** [Array] of std.array, which the calculus declares, at each list of
    arguments, as a record named by the type's own text, of one field, the list
    of its elements (generics.arrays). *)

val array_field : string
(** The field of an array's record that holds its elements. *)

val is_array : Types.ty -> bool
(** Whether the type is an array type. *)

val elements : Model_json.t -> Model_json.t
(** The list of an array's elements, the field of its record. *)

val array_of : cx -> Types.ty -> Model_json.t list -> Model_json.t
(** The array of the type whose elements are the list literal of the
    expressions. *)

val declared_record : Hir.item -> bool
(** Whether the calculus declares the record [i] as the program writes it: every
    record but the library's [Set], which the calculus has as a type of its own
    (std.sets). *)

val key : cx -> Types.ty -> bool
(** Whether the calculus has the type as a key type: an integer type, [bool],
    [str], [()], or a tuple, list, record or variant type of them whose [Eq] and
    [Hash] the program doesn't write, so that the structural impls compare it
    part by part. *)

val int_kind : Types.ty -> string option
(** The integer type's name, for an integer type. *)

val float_kind : Types.ty -> string option
(** The float type's name, for a float type. *)

val elem : Types.ty -> Types.ty
(** The element type of a list type or an array type. *)

val flat : Types.row -> bool * Types.ty option
(** Whether the calculus's row holds [io], the row holding [io] or an effect,
    and its error type. *)

val raises_in : cx -> Types.row -> (unit -> 'a) -> 'a
(** Runs the function with the row's error type as the error type of the code it
    exports, and the row as the row that code may perform. *)

val allowing : cx -> Types.row -> (unit -> 'a) -> 'a
(** Runs the function with the row as the row the code it exports may perform.
*)

val declared : cx -> Hir.item -> Types.ty list -> string
(** A record or variant type at its arguments, which the export declares: its
    name in the calculus. *)

val declared_args :
  cx -> Hir.item -> Types.ty list -> string * Model_json.t list
(** A record or variant type at its arguments: its name in the calculus, and the
    type arguments the calculus writes it with, none for a type declared at its
    arguments. *)

val record_args : cx -> Types.ty -> Model_json.t list
(** The type arguments the calculus writes a record type with. *)

val with_args : Model_json.t list -> Model_json.t list
(** The type arguments of a literal or a constructor, as its second field: none
    for a type declared at its arguments. *)

val type_params : cx -> instance -> Model_json.t
(** The type parameters of a declared type, by their names, none for a type
    declared at its arguments. *)

val instantiated : cx -> instance -> Types.ty -> Types.ty
(** A type in a declaration of the instance's type, its parameters replaced by
    the instance's arguments. *)

val args_of : Types.ty -> Types.ty list
(** A type's arguments. *)

val ty : cx -> Types.ty -> Model_json.t

val type_arg : cx -> Types.ty -> string
(** A type argument as an instance's name writes it, a value argument as
    written. *)

val record_name : cx -> Types.ty -> string
(** The name of the record the calculus declares for a record type, a declared
    one's instance or an anonymous one's own, [{ f: T, … }]. *)

val row : cx -> Types.row -> Model_json.t

val operations :
  cx -> Hir.item -> Types.ty list -> (string * Types.ty * Types.ty) list
(** An effect's operations at its arguments: each name, with its parameters as
    one type and its result. *)

val effect_key : cx -> Hir.item -> Types.ty list -> string
(** An effect at its arguments, which the export declares: its name in the
    calculus. *)

val handler_record : cx -> Types.handler -> string
(** The record that the export declares for a handler type: its name. *)

val mode : Ast.mode -> Model_json.t

val async_item : Hir.item
(** The effect [async] (tasks.async). *)
