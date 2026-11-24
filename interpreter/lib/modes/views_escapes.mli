(** Where a view escapes (views.escaping): a view leaves the scope that binds
    one of its sources nowhere, and a function only through its result, when
    every one of its sources is a [let] parameter of the function. Each escape
    is E0422, reported through [report code loc message] at the expression that
    escapes, or at the literal of a closure that captures the view and escapes.
*)

val expr :
  Env.t ->
  Views_sources.t ->
  (Code.t -> Ast.loc -> string -> unit) ->
  Tast.expr ->
  unit
(** The escapes at an expression: a closure that captures a view, given to an
    [escaping] parameter (effects.escaping-parameters); the value of a block, an
    arm or an [if let] that views a binding the block or the pattern makes; and
    the results of a closure literal that view what the closure binds itself. *)

val stmt :
  Views_sources.t ->
  (Code.t -> Ast.loc -> string -> unit) ->
  params:(Ast.mode * Hir.var) list ->
  Tast.stmt ->
  unit
(** The escape of a statement that assigns a view to one of the [inout]
    parameters [params], which goes back to the caller. *)

val body :
  Views_sources.t ->
  (Code.t -> Ast.loc -> string -> unit) ->
  params:(Ast.mode * Hir.var) list ->
  Tast.block ->
  unit
(** The escapes of a function's body whose parameters are [params]: its results,
    the final expression and each [return], which may view only its [let]
    parameters; and each assignment of a view to a variable that outlives the
    scope binding one of the view's sources. *)
