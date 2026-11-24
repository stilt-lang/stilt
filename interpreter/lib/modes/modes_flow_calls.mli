(** Closure literals, branches, jumps and loops in the walk of a body's flow
    (modes.escaping, modes.not-escaping, modes.copies and modes.shared-writes).
    Each takes the walk of expressions and blocks. *)

type walker = Modes_flow.state -> Tast.expr -> Modes_flow.into -> unit

type block_walker =
  ?id:int -> Modes_flow.state -> Tast.block -> Modes_flow.into -> unit

val closure :
  expr:walker ->
  Modes_flow.state ->
  Tast.expr ->
  Tast.pattern list ->
  Tast.expr ->
  Modes_flow.into ->
  unit
(** A closure literal copies the bindings it captures, and what holds it holds
    the copies. Its body is walked as a function of its own. *)

val branches :
  block:block_walker ->
  expr:walker ->
  Modes_flow.state ->
  Tast.expr ->
  Modes_flow.into ->
  unit
(** [if let], [match] and [try]: each part of a place that a pattern binds is a
    copy, held by its variable until its arm ends. A raise in a [try]'s operand
    goes to its arms. *)

val looping :
  block:block_walker -> expr:walker -> Modes_flow.state -> Tast.expr -> unit
(** [loop], [while] and [for], whose bodies are inside the loop: each loop's
    head is reached from before it and from the end of each turn. *)

val either : Modes_flow.state -> (unit -> unit) -> (unit -> unit) -> unit
(** Two alternatives that the walk of each function walks, after the tick where
    control chooses. *)

val leave : Modes_flow.state -> Tast.expr -> unit
(** A [break] or a [continue]. *)

val again : Modes_flow.state -> (unit -> unit) -> unit
(** Code that may run any number of times, none among them. *)

val handled : Modes_flow.state -> (unit -> unit) -> unit
(** Code from any point of which control may go on to what follows it. *)
