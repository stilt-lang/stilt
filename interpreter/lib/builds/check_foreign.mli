(** Unsafe code and what C holds, while a body is checked (c.unsafe-operations,
    c.element-types and c.lending-buffer). *)

val c_holds : Types.ty -> bool
(** Whether C holds a value of the type as Stilt does: an integer, a float,
    [bool], or a [c.Ptr] of one of them, of [()] or of another [c.Ptr]
    (c.types-c-takes and c.element-types). *)

val used : Check_state.state -> Ast.loc -> Tast.callee -> Types.ty list -> unit
(** [used st loc callee targs] records the use of [callee], called or named as a
    value at [loc] with its type arguments: E0436 for an unsafe operation
    outside every [unsafe] block (c.unsafe-operations), and, for a call that
    reads, writes or lends C memory, its [T], which {!fit} decides
    (c.element-types and c.lending-buffer). *)

val within : Check_state.state -> Ast.loc -> (unit -> 'a) -> 'a
(** [within st loc check] checks the block of the [unsafe] at [loc] with
    [check], inside it (c.unsafe-because). *)

val fit : Check_state.state -> unit
(** E0353 at each call whose [T], known by the end of the body, C doesn't hold
    as Stilt does (c.module-std-c, c.element-types and c.lending-buffer). *)
