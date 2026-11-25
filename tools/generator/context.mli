(** Where code is generated: the program so far, the scope of the code, the
    budget of the body it belongs to, and the types it can name. *)

(** {1 Programs} *)

type fn_sig = {
  fname : string;
  params : (bool * Ty.t) list;
      (** Whether each one is [inout], and its type. *)
  ret : Ty.t;
  raises : bool;  (** Whether its row is [raise<Fault>]. *)
  cost : int;  (** An estimate of the steps a call takes. *)
}

type program = {
  r : Pick.t;
  mutable decls : (string * Ty.decl) list;  (** In declaration order. *)
  mutable fns : fn_sig list;  (** The functions declared so far. *)
  mutable count : int;  (** The number in the last fresh name. *)
  fault : string;  (** The error type of every function that raises. *)
  fault_variants : (string * Ty.t list) list;  (** Its variants. *)
  panics : bool;
      (** Whether its arithmetic may panic: [+], [-] and [*] that may overflow,
          and [/] and [%] by any divisor, where every other program masks their
          operands so that they can't. *)
  capped : bool;
      (** Whether the strings and lists that its operations make are cut, so
          that no value grows without bound. *)
}

val fresh : program -> string -> string
(** A name made of [prefix] and a number that no other name has. *)

val cap_str : program -> Code.code -> Code.code
(** A string that an operation made, cut to [longest_str] bytes if the program
    is capped. *)

val cap_list : program -> Code.code -> Code.code
(** A list that an operation made, cut to [longest_list] elements if the program
    is capped. *)

val mentions : string -> string -> bool
(** [mentions word text] is whether [text] holds [word]. *)

val caps : Code.line list list -> Code.line list list
(** The declaration of the function [cap], which cuts a string, if the items
    call it, and nothing otherwise. *)

val fault : string
(** The error type of every function that raises, as its own module writes it.
*)

val fault_variants : (string * Ty.t list) list
val fault_decl : string

(** {1 Scopes} *)

type var = { name : string; ty : Ty.t; mutable_ : bool }

type scope = {
  vars : var list;  (** Latest first. *)
  frozen : string list;
      (** Variables that can't change here: those that an enclosing loop reads
          (modes.law), and loop counters. *)
  loop : bool;  (** Whether [break] and [continue] have a loop to act on. *)
  may_raise : bool;  (** Whether a raise of [Fault] may escape the code. *)
  io : bool;
  returns : Ty.t option;  (** What [return] returns, outside closures. *)
  weight : int;  (** How many times the code may run per call. *)
}
(** Where code is being generated. *)

type body = { p : program; budget : int; mutable spent : int }
(** The body being generated, and how much of its budget it has used. *)

val affordable : body -> scope -> int -> bool
(** Whether code of [cost] steps, run as often as the scope's code may run, fits
    in what is left of the budget. *)

val spend : body -> scope -> int -> unit
(** Spends the budget on code of [cost] steps in the scope. *)

val decl : body -> string -> Ty.decl
(** The declaration of a type the program declares. *)

val typed : var list -> Ty.t -> var list
(** The variables of type [ty]. *)

val declare : scope -> string -> Ty.t -> mutable_:bool -> scope
(** The scope with a variable added. *)

val changeable : scope -> var list
(** The variables that code in the scope can change. *)

val without : string list -> scope -> scope
(** The scope without the variables [names]. *)

val closure_scope : scope -> var list -> scope
(** The scope of a closure's body. It reads copies of the variables, which it
    can't change (expressions.capture), and [return], [break] and [continue]
    don't cross it. *)

(** {1 Expressions} *)

type expr = body -> scope -> depth:int -> known:bool -> Ty.t -> Code.code
(** What makes expressions, as [Expr.expr] does: [expr b sc ~depth ~known ty] is
    an expression of type [ty], at most [depth] levels deep, whose type is fixed
    without an expected type if [known]. The forms that make an expression out
    of others take it, to make their operands. *)

type forms = (int * (unit -> Code.code)) list
(** Forms that make an expression, each with its weight, as [Pick.run] takes
    them. *)

(** {1 Types} *)

val leaf_ty : Pick.t -> Ty.t
(** A number, a [bool] or a [str]. *)

val key_ty : Pick.t -> Ty.t
(** A type of map keys. *)

val random_ty : program -> ?maps:bool -> int -> Ty.t
(** A type of at most [depth] levels. With [~maps:false], no map appears in it,
    since no map has a type that is known without an expected type. *)
