(** Value parameters and value arguments (generics.value-parameters,
    generics.value-arguments and generics.constant-arguments), and the constants
    that value arguments name, computed while the program is checked. *)

open Resolve_context

val value_type : Hir.ty -> string option
(** The name of a value parameter's type: an integer type or [bool]. *)

val array_item : Hir.item
(** [Array] of [std.array] (generics.arrays). *)

val declare : ctx -> Hir.name -> Hir.ty -> ctx * Hir.var
(** [declare ctx n t] declares the value parameter [n] of the type [t], an
    integer type or [bool] (E0345), named as no value parameter or row variable
    in scope (E0208). Its module is in the meta tier (generics.meta-tier). *)

val constant_of : ctx -> Hir.name list -> Hir.item option
(** The constant that a path names where the context is, found quietly: one of a
    module, or of an inherent impl, as [Type.NAME]. *)

val value_arg : ctx -> size:bool -> string option -> Ast.ty -> Hir.ty_desc
(** [value_arg ctx ~size expected arg] reads [arg], given for a value parameter
    whose type is named [expected], or [None] when that type has an error: a
    literal of that type (E0311, E0320), a constant of it, computed (E0311,
    E0347), or a value parameter of it in scope (E0311). Anything else that
    names something is E0347, and a name that names nothing E0211
    (generics.value-arguments). When [size] tells that it is an array's size, a
    negative one is E0347 (generics.array-sizes). *)

val type_arg_misplaced : ctx -> Ast.ty -> string option
(** What a value given for a type parameter is, a literal or a value parameter,
    which is E0347 (generics.value-arguments). *)

val not_a_type : ctx -> Ast.ty -> string -> unit
(** [not_a_type ctx arg what] reports E0347 at [arg], given for a type
    parameter, which is [what]. *)
