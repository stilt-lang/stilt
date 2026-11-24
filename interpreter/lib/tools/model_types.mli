(** The types of a program as the Lean model's calculus writes them, and what an
    export has met: the record and variant types it names, and the functions it
    reaches. A form the calculus lacks raises {!Outside}. *)

exception Outside of string
(** The program uses something the model's calculus lacks, which it names. *)

val outside : ('a, unit, string, 'b) format4 -> 'a
(** Raises {!Outside} with the message. *)

type instance = { key : string; item : Hir.item; args : Types.ty list }
(** A record or variant type with its type arguments, which the calculus
    declares as a type of its own, named [key]. *)

type target =
  | Function of Hir.item
  | Member of Hir.item * string
  | Impl of Hir.item * Hir.item * string
      (** A function, a function of a type's inherent impls, or a method of the
          impl of a trait for a type constructor that the program writes. *)

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
  mutable writable : int list;
      (** The bindings of a view type that write their sources, [var]s and
          [inout] parameters (projections.writable-bindings), by their ids. *)
}

val item_name : Hir.item -> string

val param_ty : cx -> Ast.mode * Types.ty -> Model_json.t
(** The type of a parameter: an [inout] one of a view type is writable, held as
    the copy of its part (projections.writable-bindings). *)

val writes : cx -> Ast.mode -> Hir.var -> Types.ty -> unit
(** Records the binding as writable when it is an [inout] one of a view type. *)

val aliases : (int * Hir.var) list ref
(** The bindings of a [when] written as another of its names, when their handles
    reach one value (shared.names-that-may-be-one-place). *)

val var_name : Hir.var -> string

val norm : Types.ty -> Types.ty
(** The type a solved variable stands for. *)

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
(** The element type of a list type. *)

val flat : Types.row -> bool * Types.ty option
(** Whether the calculus's row holds [io], the row holding [io] or an effect,
    and its error type. *)

val raises_in : cx -> Types.row -> (unit -> 'a) -> 'a
(** Runs the function with the row's error type as the error type of the code it
    exports. *)

val declared : cx -> Hir.item -> Types.ty list -> string
(** A record type without parameters, or a variant type with its arguments,
    which the export declares: its name in the calculus. *)

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
