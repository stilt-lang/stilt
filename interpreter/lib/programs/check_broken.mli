(** Which bodies of a program have an error, as program.bodies-with-errors
    defines it for [run]: those in whose declaration an error lies, whether or
    not errors.root-causes reports it, and those that meet the error type,
    through a name with an error elsewhere or a declaration whose signature
    holds it. *)

val mark :
  Env.t ->
  Hir.program ->
  Tast.program ->
  errors:Diagnostic.t list ->
  extents:(string * Syntax_parts.extent list) list ->
  recovered:(string * Ast.loc) list ->
  Tast.program
(** [mark env hir program ~errors ~extents ~recovered] is [program] with every
    body that has an error replaced by [Broken]. [errors] are the program's
    errors, [extents] the items of each file, and [recovered] the functions,
    constants and tests, by file and name, that a part of a file with a syntax
    error declares with an error. *)

val constant_loc : Hir.program -> Hir.item -> (string * Ast.loc) option
(** The file and the name of a constant's declaration. *)

val member_constant_loc :
  Hir.program -> Hir.item -> string -> (string * Ast.loc) option
(** The file and the name of the declaration of a type constructor's associated
    constant. *)

val impl_constant_loc :
  Hir.program -> Hir.item -> Hir.item -> string -> (string * Ast.loc) option
(** [impl_constant_loc hir trait owner name] is the file and the name of the
    declaration of the constant [name] of the impl of [trait] for [owner]
    (traits.impl-members). *)
