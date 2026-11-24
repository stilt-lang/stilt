(** The words of facts.acceptance-places and facts.known-signs that read code
    alone: places, what a test compares and the facts each test gives, the keys
    of facts.keys, the literals and constants of facts.terms, and the code that
    can't complete. *)

type num = { neg : bool; mag : int64 }

val num_of_literal : string -> num
(** The number an integer literal writes. *)

val negate : num -> num
(** [-n], zero staying zero. *)

val compare_num : num -> num -> int
(** Compares two numbers by their values. *)

val zero : num
(** The number 0. *)

val sign : num -> int
(** -1, 0 or 1, as [n] is below, at or above zero. *)

type place = { root : int; fields : string list }
type term = Name of int | Num of num | Len of place | Other

type key =
  | Key_name of int
  | Key_int of num
  | Key_str of string
  | Key_bool of bool

type cmp = Lt | Le | Gt | Ge | Eq | Ne

type atom =
  | Cmp of term * cmp * term
  | Non_empty of place
  | Contains of place * key

type reader = {
  constant : Tast.expr -> num option;
  whens : (int, unit) Hashtbl.t;
}

val mirrored : cmp -> cmp
(** The comparison with its operands swapped: [Lt] for [Gt]. *)

val compares : atom -> term -> cmp -> term -> bool
(** Whether [atom] compares [a] with [b] by [op], written either way round. *)

val is_int : Types.ty -> bool
(** Whether a type is an integer type. *)

val divides : Tast.expr -> Tast.expr -> bool
(** effects.panicking-operations: whether dividing [a] by [b] can panic, an
    integer division whose divisor isn't written as an integer literal other
    than zero. *)

val is_map : Types.ty -> bool
(** Whether a type is a [Map]. *)

val is_list : Types.ty -> bool
(** Whether a type is a [List]. *)

val is_sequence : Types.ty -> bool
(** Whether a type is a [List] or an array of [std.array]. *)

val unwrap : Tast.expr -> Tast.expr
(** The expression inside a [comptime] or an instantiation, as the rules read
    it. *)

val place : reader -> Tast.expr -> place option
(** The place an expression names: a local that no [when] holds, and the fields
    read from it. *)

val binding : reader -> Tast.expr -> Hir.var option
(** The local an expression is, unless a [when] holds it. *)

val name : reader -> Tast.expr -> Hir.var option
(** The local of integer type an expression is, as a term of facts.terms names
    it. *)

val number : reader -> Tast.expr -> num option
(** The integer an expression is: a literal, a negated literal, or a constant
    the reader knows. *)

val method_name : Tast.callee -> string option
(** The name of the method a call calls, if it calls one. *)

val is_map_method : string -> Tast.callee -> bool
(** Whether a call calls the method [name] of [Map]. *)

val len_of : reader -> Tast.expr -> place option
(** The place whose [len()] an expression is. *)

val term : reader -> Tast.expr -> term
(** An expression as a term of facts.terms: a name, a number, a length, or
    other. *)

val key : reader -> Tast.expr -> key option
(** An expression as a key of facts.keys: a local, or an integer, string or
    boolean literal. *)

val gives : reader -> Tast.expr -> bool -> atom list
(** The facts a condition gives where it is true, or where it is false: each
    conjunct of its [&&] chain, and for its negation each disjunct's of its [||]
    chain, read through [!]. *)

val stored : reader -> Tast.stmt -> (place * key) option
(** The store of a key that a statement is, [m[k] = v] or [m.insert(k, v)]. *)

val stored_if_missing : reader -> Tast.stmt -> (place * key) option
(** The key that an [if !m.contains(k) { …; m[k] = v }] statement stores. *)

val ends_block : Tast.block -> bool
(** Whether code can't complete: each of its paths ends in [return], [break],
    [continue], [raise] or a call of type [Never]. *)
