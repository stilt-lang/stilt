(** The JSON that the Lean model reads (formal/Stilt/Run/Decode.lean): each
    constructor an array of its name and its fields, a constructor without
    fields its name alone. *)

type t =
  | Str of string
  | Arr of t list
  | Bool of bool
  | Null
  | Obj of (string * t) list

val tag : string -> t list -> t
(** [tag name fields] is the constructor [name] with its [fields]. *)

val to_string : t -> string
