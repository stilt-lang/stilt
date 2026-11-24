(** The tree form of a syntax tree, as [stilt-ref parse --sexp] prints it.
    [reference/03-syntax.md] defines the form of every node (syntax.tree-form).
*)

val of_module : Ast.module_ -> string
(** A module's tree as one line, with no trailing newline. *)

val of_expr : Ast.expr -> string
(** An expression's tree as one line, with no trailing newline. *)

val binary : Ast.binary -> string
(** A binary operator as it is written, such as [+%]. *)

val quote : string -> string
(** A string as a quoted atom, escaped as std.show-names-and-escapes escapes a
    string nested inside another value. *)
