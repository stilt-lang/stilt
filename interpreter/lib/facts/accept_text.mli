(** The text of what E0204 says the rule of acceptance closest to an operation
    needs (facts.closest-rule), with each expression written back from the typed
    program as the compiler writes it. *)

val expr : Env.t -> Tast.expr -> string
(** An expression's text, a block and any other form that holds one as [{ … }].
*)

val range_closures : string
val range_form : Hir.var -> string
val range_start : string
val range_start_at : Env.t -> Tast.expr -> string

val range_end :
  Env.t ->
  Tast.expr ->
  Tast.expr option ->
  Tast.expr ->
  inclusive:bool ->
  string
(** [range_end env list k end ~inclusive]: an end other than [list.len()], or
    [list.len() - k], written after [..=] where the range includes it. *)

val range_length : Env.t -> Tast.expr -> int -> string
val guard_form : string
val guard_lower : Env.t -> Tast.expr -> string
val guard_upper : Env.t -> Tast.expr -> Tast.expr -> string
val guard_writes : Env.t -> Tast.expr -> int -> string
val guard_length : Env.t -> Tast.expr -> int -> string
val divisor_form : string
val divisor_test : Env.t -> Tast.expr -> string
val divisor_writes : Env.t -> Tast.expr -> int -> string
val key_form : string
val key_type : string
val key_test : Env.t -> Tast.expr -> Tast.expr -> string
val key_writes : Env.t -> Tast.expr -> int -> string
val key_changes : Env.t -> Tast.expr -> int -> string
val loop_comparison : string
val loop_var : string
val loop_bound : int option -> string
val loop_step : Hir.var -> bool -> string
val loop_continue : Env.t -> Hir.var -> bool -> Tast.expr -> int -> string
val loop_writes : Hir.var -> int -> string
val shrink_form : string
val shrink_test : Hir.var -> bool -> int -> string
