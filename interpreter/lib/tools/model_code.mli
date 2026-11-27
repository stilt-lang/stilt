(** The code that the export writes of its own, for the structural impls that
    reach an impl the program writes and for maps whose keys have such impls:
    what each computes, the functions it declares, and the expressions they are
    built of. *)

(** What a structural impl computes: [Eq.eq], [Ord.compare], [Hash.hash], or
    [Show.show], nested in another value or not (traits.show). *)
type kind = Eq | Compare | Hash | Show of bool

type at = kind -> Types.ty -> Model_json.t list -> Model_json.t
(** How the export writes a prelude trait's function at a type, on its operands.
*)

val bool_ty : Types.ty
val i64 : Types.ty
val str_ty : Types.ty
val ordering_ty : Types.ty
val u64 : Types.ty
val hash_trait : Hir.item

val result_of : kind -> Types.ty
(** The type of what the trait's function gives. *)

val name_of : kind -> string
(** The trait's function, [Trait.m], as the name of a function of the export's
    names it. *)

val int : int -> Model_json.t
(** An [i64] literal. *)

val false_e : Model_json.t
val true_e : Model_json.t
val field_e : Model_json.t -> string -> Model_json.t

val let_e :
  Model_types.cx ->
  string ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** [let n: t = init] followed by [body]. *)

val var_in :
  Model_types.cx ->
  string ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** [var n: t = init] followed by [body]. *)

val assign : string -> Model_json.t -> Model_json.t
(** [n = v]. *)

val when_e : Model_json.t -> Model_json.t -> Model_json.t
(** [if c { x }], of type [()]. *)

val not_e : Model_json.t -> Model_json.t
val and_e : Model_json.t -> Model_json.t -> Model_json.t
val list_len : Model_json.t -> Model_json.t

val incr : string -> Model_json.t
(** [n = n + 1], on an [i64]. *)

val concat : Model_json.t list -> Model_json.t
(** The texts joined. *)

val ordering : Model_types.cx -> string -> Model_json.t
(** The [Ordering] of that constructor. *)

val same_ordering : Model_types.cx -> Model_json.t -> string -> Model_json.t
(** Whether an [Ordering] is the one of that constructor. *)

val helper_call :
  Model_types.cx -> string -> Model_json.t list -> Types.ty -> Model_json.t
(** A call of a function the export declares, by its key, on its arguments, with
    the type of its result. *)

val declare :
  Model_types.cx ->
  string ->
  (string * Types.ty) list ->
  Types.ty ->
  (unit -> Model_json.t) ->
  unit
(** [declare cx key params result body] declares the function [key] of the
    export's own, once, its body written after the key is among the helpers, so
    that the body may call it. *)

val joined :
  Model_types.cx ->
  Types.ty ->
  Model_json.t ->
  (Model_json.t -> Model_json.t) ->
  string * string ->
  Model_json.t
(** [joined cx elem iterable show (opening, closing)]: the texts that [show]
    gives each element of [iterable], of type [elem], joined by [, ] between
    [opening] and [closing]. *)

val separated : Model_json.t list -> Model_json.t list
(** Texts with [, ] between them. *)

val mix : Model_json.t -> Model_json.t -> Model_json.t
(** A hash with another mixed in, wrapping. *)

val native_ordering :
  Model_types.cx -> Model_json.t -> Model_json.t -> Model_json.t -> Model_json.t
(** [Less], [Greater] or the last, as the first [i64] is below, above or equal
    to the second. *)

val ctor_arm :
  string ->
  string * 'a list ->
  string ->
  (Model_json.t list -> Model_json.t) ->
  Model_json.t
(** [ctor_arm t (c, payload) base body]: the arm [C(base/0, …) => body] of a
    [match] on the variant type [t], its payload bound to fresh names. *)
