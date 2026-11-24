(** The print of a typed body, which two bodies share exactly when they are the
    same body (docs.same-body). *)

val print : params:Hir.var list -> Tast.block -> string
(** [print ~params block] is the print of a function's block whose parameters,
    its receiver's first, are [params]: each construct with its literals,
    operators, fields, modes of arguments and format specs; each declaration it
    names; each local by its number, in the order the body binds them, its
    parameters first, with its type; and each literal's and type argument's
    type, type parameters by name and function types without their rows. *)
