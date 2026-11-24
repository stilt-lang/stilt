(** The shapes of types (meta.shapes), which the evaluator builds and the checks
    of meta.types-without-shape and meta.unseen-instantiations walk. *)

(** The case of a type's shape, with the types it holds. *)
type case =
  | Leaf of string  (** [Int], [Float], [Bool], [Str] or [Unit]. *)
  | Holds of string * Types.ty list
      (** [Option], [List], [Set] or [Array] with its element type, or [Map]
          with its key and value types. *)
  | Fields of string * (string * Types.ty) list
      (** [Tuple] or [Record], with each field's name and type, in order. *)
  | Cases of (Hir.item * Types.ty list) list
      (** [Variants], with each variant and its payload's types, in order. *)

val case_of : Env.t -> Types.ty -> case option
(** The case of a type's shape, the first of meta.shapes that fits, or [None]
    for a type without a shape (meta.types-without-shape). *)

val name : case -> string
(** The case's name, as [Shape] names it. *)

val parts : case -> Types.ty list
(** The types that a value of the case's type holds directly: its elements, its
    keys and values, its fields or its payloads' fields, in order. *)

val payload : Env.t -> Types.ty -> string -> Types.ty option
(** [payload env ty name] is the type of the payload of the case [name] of
    [Shape<ty>], with its fresh types the types that [ty] holds. *)

val describe : Types.ty -> string
(** A type as a diagnostic writes it, as [T.name()] gives it
    (meta.shape-and-name). *)
