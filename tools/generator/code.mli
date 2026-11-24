(** Source code: the text of expressions, and lines of code with their depth of
    nesting, as a program prints them. *)

type code = { text : string; atom : bool; known : bool }
(** An expression's text. [atom] tells whether it can be an operand or a
    receiver without parentheses. [known] tells whether its type is fixed
    without an expected type, as a receiver's must be (types.known-types). *)

val atom : ?known:bool -> string -> code
(** An expression that is an operand as it stands, whose type is known unless
    [~known:false]. *)

val compound : ?known:bool -> string -> code
(** An expression that an operand or a receiver puts in parentheses. *)

val operand : code -> string
(** The text of an expression as an operand or a receiver. *)

val head : string -> string
(** [text] as the head of an [if], [while] or [match], or the iterable of a
    [for], which end at their first [{] outside brackets (expressions.heads). *)

val call_text : string -> string list -> string
(** [call_text name args] is [name(args)]. *)

val method_on : code -> string -> string list -> code
(** [method_on recv name args] is [recv.name(args)]. *)

type line = int * string
(** A line of code, with its depth of nesting. *)

val nest : line list -> line list
(** The lines, one level deeper. *)

val line : string -> line list
(** One line, at depth 0. *)

val block_lines : string -> line list -> string -> line list
(** [opening], the lines one level deeper, then [closing]. *)

val render : line list -> string
(** The text of the lines, each indented by two spaces per level. *)
