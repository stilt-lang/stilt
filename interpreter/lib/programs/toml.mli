(** TOML 1.0, which manifests are written in (packages.manifest). The parser
    keeps the place of every key and value, which manifest errors are reported
    at. *)

(** How a table came to be, which decides how it may be added to. *)
type defined =
  | Implicitly  (** As the super-table of a header, [a] for [[a.b]]. *)
  | Header  (** By a header. *)
  | Dotted  (** By dotted keys. *)
  | Inline  (** As an inline table, which nothing adds to. *)

type value = { at : int; end_ : int; kind : kind }
(** A value, from its first byte to the byte after its last. *)

and kind =
  | String of string
  | Integer
  | Float
  | Bool
  | Datetime
  | Array of value list
  | Table of table
  | Tables of table list  (** An array of tables. *)

and table = {
  mutable defined : defined;
  mutable entries : entry list;  (** In the order of their definitions. *)
  mutable last : int;
      (** The end of its last key-value pair, or of its header. *)
}

and entry = { key : string; key_at : int; mutable value : value }

val describe : kind -> string
(** The kind of value, as errors name it, such as "a string". *)

val get : table -> string -> entry option

val parse : string -> (table, int * string) result
(** The root table of a TOML 1.0 document, or the byte offset of the first place
    from which the text isn't TOML 1.0, with why. A key or table defined twice
    is an error at the first character of the key that defines it again. *)
