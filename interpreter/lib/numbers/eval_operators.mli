(** The operators on numbers and booleans (numbers.no-implicit-conversions,
    numbers.comparisons and numbers.ieee-754). *)

val truth : Value.value -> bool
(** The boolean a [bool] value holds. *)

val arithmetic :
  Eval_state.frame ->
  Ast.loc ->
  Ast.binary ->
  Types.ty ->
  Value.value ->
  Value.value ->
  Value.value
(** [arithmetic fr loc op ty a b] is [a op b] for an arithmetic or bitwise
    operator on two numbers of type [ty]. An integer operation that fails, such
    as one that overflows, panics at [loc]. *)

val shift :
  Eval_state.frame ->
  Ast.loc ->
  Ast.binary ->
  Types.ty ->
  amount:Types.ty ->
  Value.value ->
  Value.value ->
  Value.value
(** [shift fr loc op ty ~amount a b] is [a op b] for a shift of an integer of
    type [ty] by an integer of type [amount] (numbers.shifts). An amount out of
    range panics at [loc]. *)

val unary :
  Eval_state.frame ->
  Ast.loc ->
  Ast.unary ->
  Types.ty ->
  Value.value ->
  Value.value
(** [unary fr loc op ty v] is [op v], for a [v] of type [ty]. A negation that
    overflows panics at [loc]. *)
