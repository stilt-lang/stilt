(** Shared writes (modes.copies and modes.shared-writes): the modifications of a
    [var] binding or an [inout] parameter while a copy of the modified part, or
    a copy of that copy, may still last. *)

type shared = {
  place : Tast.expr;
      (** The place modified: an assignment's, a [yield]'s, or an [inout]
          argument's, receivers included; or a [when] that gives its names'
          values back to their handles, or a call of [Shared.new]
          (modes.handles). *)
  binding : Hir.var option;  (** The binding modified. *)
  holder : Hir.var option;  (** The binding that holds the copy, if one does. *)
}

val escapes : Modes_flow.t -> int list
(** The bindings that aren't parameters and escape (modes.escaping and
    modes.not-escaping). *)

val shared : Modes_flow.t -> shared list
(** Each shared modification of a body, in source order. *)
