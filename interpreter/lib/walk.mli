(** Traversals of the elaborated program, shared by the later phases of
    checking. *)

(** What an expression holds directly. *)
type part = Expr of Tast.expr | Block of Tast.block

val parts : Tast.expr -> part list
(** The expressions and blocks directly inside an expression, in the order they
    are written: its operands and arguments, its blocks, and the guards and
    bodies of its arms. *)

val catch_arms : Tast.catch option -> Tast.arm list
(** The arms of a [catch], if there is one. *)

val stmt_exprs : Tast.stmt -> Tast.expr list
(** The expressions directly inside a statement, in order. *)

val block_exprs : Tast.block -> Tast.expr list
(** The expressions directly inside a block's statements, in order. *)

val children : Tast.expr -> Tast.expr list
(** The expressions directly inside an expression or its blocks, in order. *)

val iter : ?stmt:(Tast.stmt -> unit) -> (Tast.expr -> unit) -> Tast.expr -> unit
(** [iter f e] applies [f] to [e] and to every expression inside it, each before
    the expressions inside it, in the order they are written, closures included.
    [stmt] is applied to every statement on the way. *)

val iter_block :
  ?stmt:(Tast.stmt -> unit) -> (Tast.expr -> unit) -> Tast.block -> unit

val exists : (Tast.expr -> bool) -> Tast.expr -> bool
(** Whether the expression, or an expression inside it, satisfies the predicate.
*)
