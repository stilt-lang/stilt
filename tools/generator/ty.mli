(** The types of generated programs, and what the Reference says each one can
    do. *)

type int_kind = I8 | I16 | I32 | I64 | U8 | U16 | U32 | U64
type float_kind = F32 | F64

type t =
  | Int of int_kind
  | Float of float_kind
  | Bool
  | Str
  | Unit
  | Tuple of t list
  | List of t
  | Map of t * t
  | Option of t
  | Named of string  (** A record or variant type that the program declares. *)

(** A declared type: a record's fields, or a variant type's variants with their
    payloads. *)
type decl = Record of (string * t) list | Variants of (string * t list) list

val int_kinds : int_kind list
val float_kinds : float_kind list

val int_name : int_kind -> string
(** The name of an integer type, such as [i64]. *)

val float_name : float_kind -> string
(** The name of a float type, such as [f64]. *)

val bits : int_kind -> int
(** The width of an integer type, in bits. *)

val signed : int_kind -> bool

val to_string : t -> string
(** A type as programs write it. *)

val map_named : (string -> string) -> t -> t
(** [t] with [f] applied to the name of every declared type in it. *)

val named : t -> string list
(** The names of the declared types in [t]. *)

val widens : from:int_kind -> into:int_kind -> bool
(** Whether every value of [from] fits in [into], so that [.to_T()] returns [T]
    rather than [Option<T>] (numbers.conversions). *)

val ordered : decls:(string * decl) list -> t -> bool
(** Whether [t] has [Ord] structurally (traits.structural-impls). Floats do,
    through their total order, and maps don't. *)

val has_map : (string * decl) list -> t -> bool
(** Whether a map appears anywhere in [t]. *)
