(** The types of a body: the signatures it instantiates, and the types it writes
    and names (types.inferred-per-body and types.known-types). *)

val pairs : Env.fn_sig -> (Hir.var * Tast.label) list
(** The row variables that a signature pairs with an error type, with that type
    (effects.paired-row-variables), or with an effect that a row holds beside
    them (handlers.with-pairing). *)

val instantiate :
  ?fixed:(Hir.var * Types.ty) list ->
  Check_state.state ->
  Ast.loc ->
  Env.fn_sig ->
  self:(Hir.var * Types.ty) option ->
  use_at:Ast.loc ->
  Types.ty list * (Types.mode * Types.ty) list * Types.ty * Types.row
(** A signature's type arguments, parameters, return type and row, with fresh
    variables for its type and row parameters, [self]'s type for [Self], and
    [fixed]'s for a trait's parameters (traits.trait-arguments). The type
    parameters' bounds become obligations, with the arguments they give
    (traits.bound-arguments), and the use at [use_at] records what it gives the
    row variables that the signature pairs (effects.passing-to-paired-variables
    and effects.what-paired-variable-may-raise). *)

val instantiate_poly :
  Check_state.state -> Ast.loc -> Types.forall -> Types.ty list * Types.ty
(** A polymorphic function type at a use: the fresh variables its type
    parameters take, which meet their bounds there, and its body with them in
    place (polymorphism.instantiation). *)

val instantiate_type :
  Check_state.state ->
  Ast.loc ->
  Hir.item ->
  Types.ty * Types.ty list * Env.type_info
(** A type constructor applied to fresh variables, the variables, and what the
    constructor is. *)

val of_hir : Check_state.state -> Hir.ty -> Types.ty
(** A type written in the body. An error in it is an error of the body
    (errors.error-type). *)

val named_type : Check_state.state -> Hir.ty -> Types.ty
(** A type named in an expression or a pattern, whose arguments inference
    supplies (declarations.type-arguments). *)
