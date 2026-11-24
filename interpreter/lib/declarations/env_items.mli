(** The signatures of every module's items: its types and their variants,
    functions, constants and traits (declarations.function-declarations,
    traits.declaring-trait and handlers.declaring-effect). *)

val synthetic : ?loc:Ast.loc -> string -> Hir.var
(** A new variable that no declaration has. *)

val decl_name : Hir.decl Hir.node -> Hir.name
(** The name of a declaration other than a test. *)

val declare_items : Hir.program -> Env_tables.t
(** The environment of the items of every module and of the built-in types of
    [std.prelude], without impls. Of two items with the same name, names refer
    to the first, and resolution reports the other. *)
