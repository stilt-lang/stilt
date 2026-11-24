(** The paths that execution may take through a body, which modes.shared-writes
    reads its conditions along: from one tick of the flow to another, avoiding
    the ticks where a binding is assigned or bound anew, and staying inside a
    block. *)

(** What ends a path at a tick: nothing, an assignment of the whole binding or a
    binding of it anew, or that or an assignment of a place of the binding that
    holds the place at the path. *)
type kill = Nothing | Whole of int | Covering of int * Modes_places.step list

type t

val make : Modes_flow.t -> t
(** The paths of a flow, ended by none of its assignments yet. *)

val ended_by : t -> (int * Modes_places.step list * int * int) list -> t
(** The same paths, which these assignments end, each with its binding, the
    place's path, and the ticks where its value starts and where it is assigned.
    An assignment whose value holds the tick a path starts from doesn't end it.
*)

val reaches : t -> ?kill:kill -> ?within:int * int -> int -> int -> bool
(** Whether a path goes from the first tick to the second, with no tick that
    [kill] ends after the first, and that doesn't leave [within], from its first
    tick to its last, once it is inside. *)
