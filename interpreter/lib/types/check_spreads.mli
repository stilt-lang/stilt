(** Spread expressions, which map over the tuples of a pack
    (variadics.spread-expressions and variadics.pack-tuples). *)

val is_spread : Hir.expr -> bool

val spread : Check_state.ctx -> Ast.loc -> Hir.expr -> Tast.expr
(** [..e], whose type is the spread of its pack over [e]'s type. The pack tuples
    [e] names stand for their elements in it; it names at least one, all of one
    pack, and stands inside no other spread (E0343). *)

val names_local : Check_state.state -> Types.ty -> unit
(** Notes that a spread being checked names a local of this type, so that a
    spread naming one whose type holds the error type gets no E0343 of its own
    (errors.error-type). *)

val named_in_spread :
  Check_state.state ->
  Ast.loc ->
  Hir.var ->
  Types.ty ->
  Types.ty ->
  Tast.expr option
(** [named_in_spread st loc v pack element] is the use of the pack tuple [v], of
    [pack], inside a spread being checked: [v] as its [element], or E0343 inside
    a closure there. [None] outside every spread. *)

val in_closure : Check_state.state -> (unit -> 'a) -> 'a
(** Runs the check of a closure's body, which inside a spread names no pack
    tuple. *)

val spread_tuple : Check_state.ctx -> Ast.loc -> Hir.expr list -> Tast.expr
(** A tuple with spreads among its elements, as [(..e, x)]. *)

val spread_list :
  Check_state.ctx -> Types.ty option -> Ast.loc -> Hir.expr list -> Tast.expr
(** A list with spreads among its elements, as [[..e]], whose values' type names
    no pack, so that every element has it (E0311). *)

val spread_arguments :
  Check_state.ctx ->
  Ast.loc ->
  (Ast.mode * Types.ty) list ->
  Hir.arg list ->
  Tast.arg list
(** The arguments of a call where the parameters or the arguments hold a spread,
    which give a pack its elements from the arguments' types
    (variadics.pack-inference and variadics.spread-expressions). *)
