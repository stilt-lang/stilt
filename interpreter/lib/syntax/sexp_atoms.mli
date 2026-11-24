(** The atoms of the tree form of a syntax tree, as [stilt-ref parse --sexp]
    prints it, and the token trees of macros. *)

type t = Atom of string | List of t list

val to_string : t -> string
(** The tree form, its lists in parentheses and their items separated by spaces.
*)

val quote : string -> string
(** [text] as a string literal, its quotes, backslashes and control characters
    escaped. *)

val str : string -> t
(** The atom of [text] as a string literal. *)

val tagged : string -> t list -> t
(** The list of [tag] and [items]. *)

val name : Ast.name -> t
(** The atom of a name, as written. *)

val path : Ast.path -> t
(** The atom of a path, its names joined by dots. *)

val with_mode : Ast.mode -> t -> t
(** [tree], tagged [inout] when its mode is. *)

val atom : Ast.atom -> t
(** A macro's token as written, and a literal or a piece of an interpolated
    string as a string of its text. *)

val tree : Ast.tree -> t
(** A macro's token tree: each token as [atom] writes it, each group tagged by
    its brackets, each fragment tagged [frag] and each repetition [rep], with
    its separator, [_] for none, and its operator. *)

val macro_arm : Ast.macro_arm -> t
(** An arm of a pattern macro, tagged [arm]: its pattern, the fragment its block
    binds if it has one, and its template, tagged [template]. *)

val binary : Ast.binary -> string
(** The spelling of a binary operator. *)
