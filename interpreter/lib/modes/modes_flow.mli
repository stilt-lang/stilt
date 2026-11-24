(** The flow of values through a body, which locality and uniqueness read
    (modes.escaping, modes.not-escaping, modes.copies and modes.shared-writes):
    where a binding's value, or a part of it with a copy-on-write type, leaves
    the function, where a copy of it is made and what holds the copy, and where
    a [var] or an [inout] parameter is written. Positions are ticks, counted in
    source order; a binding lasts until the block that holds it ends. The ticks
    are the points of the paths that execution may take: each goes on to the
    next unless the walk cuts it, and jumps, branches and loops add their own
    steps. *)

(** What declares a binding. *)
type kind =
  | Let
  | Var
  | Param of Ast.mode
      (** A parameter of the function or of a closure literal, with its mode. *)
  | Pattern  (** A pattern of a [match], an [if let], a [for] or a [catch]. *)

(** How long something lasts. *)
type extent =
  | Here  (** While the expression that holds it is evaluated. *)
  | Rest  (** For the rest of the function. *)
  | Scope of int  (** Until the block with this number ends. *)

type point = {
  tick : int;
  blocks : int list;  (** The blocks around it, innermost first. *)
}

type decl = {
  var : Hir.var;
  kind : kind;
  frame : int;  (** The function, 0, or the closure literal it belongs to. *)
  scope : extent;
}

(** What holds a copy, which decides how long it lasts (modes.copies). *)
type holder =
  | Bound of Hir.var list * extent  (** Bindings, until their scope ends. *)
  | Place of Hir.var  (** The binding that an assigned place is part of. *)
  | Until of extent  (** Nothing a binding names. *)

type copy = {
  binding : int;
  path : Modes_places.step list;
  made : point;
  came : int;
      (** The tick where it came into its holder: where it was made, or for a
          copy of a copy, where the later copy was made. *)
  holder : holder;
  stored : bool;
      (** Whether it is stored in a value, captured or kept in a call's result,
          rather than bound by a pattern itself, so that it lasts for the rest
          of the function when what holds it escapes. *)
  at : Modes_places.step list option;
      (** The place inside the holder's value where the copy is, if it is one
          there: [[]] for a copy that is the holder's whole value. *)
  wide : bool;
      (** Whether copies of copies around a cycle may give the holder a deeper
          part, or the part at another place, than [path] and [at] say, so that
          it may hold a copy of any part below [path]. *)
}

type write = {
  target : int;
  wpath : Modes_places.step list;
  at : point;
  place : Tast.expr;  (** The place written, as the body holds it. *)
  replaces : bool;
      (** Whether it assigns the place, replacing what was there rather than
          writing inside it. *)
}
(** A modification of a part of a binding, other than an assignment of all of it
    (modes.kinds-of-access). *)

type t = {
  decls : (int, decl) Hashtbl.t;
  mutable escapes : int list;
      (** The bindings that aren't parameters and escape by themselves. *)
  mutable kept : int list;
      (** The parameters that leave the function, or that [var] rebinds: those
          it consumes (values.consumed-parameters). *)
  mutable held : (int list * int list) list;
      (** For each closure literal that bindings hold, those bindings and the
          bindings it captures, which escape when one of its holders does. *)
  mutable copies : copy list;
  mutable writes : write list;
  mutable assigned : (int * Modes_places.step list * int * int) list;
      (** Each assignment of a binding or a place of it, which replaces the
          value there: the binding, the place's path, and the ticks where the
          value starts and where it is assigned. *)
  mutable reads : (int * point) list;
      (** Each read of a place, by its root binding, where it is. *)
  mutable selves :
    (int * Modes_places.step list * Modes_places.step list option * int) list;
      (** Each part of a binding's own value that a value assigned to the whole
          binding holds: the binding, the part's path, its place inside the
          value if it has one, and where it is read (modes.shared-writes). *)
  mutable bound : (int * int) list;
      (** Where each binding is bound, which starts it anew: a loop's next turn
          binds the bindings of its body again. *)
  mutable spans : (int * (int * int)) list;
      (** The ticks of each block, by its number: the first and the last. *)
  cut : (int, unit) Hashtbl.t;
      (** The ticks that don't go on to the next one. *)
  jumps : (int, unit) Hashtbl.t;
      (** The ticks of [break], [continue], [return] and raises, which go only
          where their own steps say. *)
  mutable steps : (int * int) list;
      (** The steps from one tick to another, other than to the next. *)
  mutable ranges : (int * int * int) list;
      (** Each tick from the first to the second may go to the third: a raise to
          a [catch], or a performance that isn't resumed to the end of its
          [with]. *)
  mutable ticks : int;  (** The last tick of the body. *)
  mutable joined : (int * int) list;
      (** Each pair of names of one [when] whose values have the same type,
          which may be one place (modes.shared-when-names). *)
  mutable handed : write list;
      (** Each call of [Shared.new], as a write of the binding whose value it is
          given, which shares it with the handle (modes.handles). *)
}

type target = {
  head : int;
  mutable breaks : int list;
  mutable continues : int list;
}
(** A loop around the code walked: its head, and its [break]s and [continue]s so
    far. *)

type calls = {
  consumed : Tast.callee -> int list;
      (** The parameters a callee consumes, by their positions, a receiver
          first. *)
  may_store : Types.ty -> Types.ty list -> bool;
      (** Whether a call may store an argument of the first type in a value of
          one of the others, its result's and its [inout] arguments'
          (modes.call-stores). *)
  cow : Types.ty -> bool;
}

(** How a value leaves the function: returned, raised or yielded, or kept in
    something that does. *)
type how = Out | Kept

type into = {
  leaves : how option;
  held_by : holder option;
  result : holder option;
      (** What holds the result of a call that consumes the value. *)
  pattern : Tast.pattern option;  (** The pattern that binds the value. *)
  lasts : extent;  (** How long a value there lasts when nothing holds it. *)
  at : Modes_places.step list option;
      (** Where the value sits inside the value of what holds it, if it is a
          place there. *)
}
(** Where the value of an expression goes. *)

type state = {
  calls : calls;
  flow : t;
  mutable frame : int;
  mutable frames : int;
  mutable tick : int;
  mutable blocks : int list;
  mutable block_count : int;
  mutable passed :
    (Hir.var * Modes_places.step list * point * holder * Tast.expr) list;
      (** The places passed to the consumed parameters of the call being walked,
          which it copies if it loses their reuse. *)
  mutable targets : target list;  (** The loops of the frame, innermost first. *)
}

val create : calls -> state
val holders : holder -> Hir.var list
val read : extent -> into
val leaving : how -> into

val keeper : into -> holder
(** What holds a value made where [into] says, such as a literal or a closure.
*)

val point : state -> point
(** The next position. *)

val fresh_block : state -> int

val meet : ?jumps:int list -> state -> int list -> int
(** A new tick that control reaches only from the ticks [froms], the ends of the
    paths that meet there, unless one is a jump, and from the jumps [jumps]. *)

val jump : state -> int
(** A new tick that goes on to nothing that follows it in the source. *)

val step : state -> int -> int -> unit
(** A step from the first tick to the second, unless the first is a jump. *)

val bind_at : state -> Hir.var list -> unit
(** Where bindings are bound. *)

val join_names : state -> (Tast.expr * Hir.var) list -> unit
(** Records the pairs of a [when]'s names whose values have the same type
    (modes.shared-when-names). *)

val spanning : state -> int -> (unit -> 'a) -> 'a
(** Records the ticks that a block, by its number, walked by the function,
    holds. *)

val declare : state -> Hir.var -> kind -> extent -> unit

val own : state -> Hir.var -> decl option
(** The declaration of a binding of the frame being walked. *)

val copy :
  ?at:Modes_places.step list option ->
  state ->
  int ->
  Modes_places.step list ->
  point ->
  holder ->
  bool ->
  unit
(** Records a copy of a part of a binding, made at a point, held by a holder,
    and whether it is stored; [at] is its place inside the holder's value, if it
    has one. *)

val write : ?replaces:bool -> state -> Tast.expr -> unit
(** Records a modification of a place, if the expression is one. *)

val pattern_parts :
  Tast.pattern ->
  Modes_places.step list ->
  (Modes_places.step list * Hir.var * Types.ty) list
(** The parts of the place at a path that a pattern binds, each with the
    variable that binds it and its type. *)

val binders : Tast.pattern -> Hir.var list
