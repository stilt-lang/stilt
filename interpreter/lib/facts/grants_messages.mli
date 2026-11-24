(** The facts of a package's own code that a manifest grants, and the message of
    E0608 (packages.ungranted-effects; facts.ungranted-capabilities;
    c.granting-unsafe). *)

(** A fact that a grant covers: a capability, [io] without one, or an [unsafe]
    block. *)
type fact = Has of Ast.capability | Bare | Unsafe_code

val narrowest : fact list -> string
(** The narrowest [may] that grants every fact of a dependency's own code: its
    capabilities, in the order of facts.capabilities, or [io] alone when it
    performs [io] without one, as [may = ["console", "fs"]], then [unsafe] when
    it holds an [unsafe] block. *)

val ungranted :
  string ->
  facts:fact list ->
  fact ->
  string ->
  Implicit_names.key * Ast.loc ->
  string
(** [ungranted dep ~facts fact path (callee, at)]: the message of an entry for
    [dep], whose own code has [facts], that doesn't grant [fact], which the
    function at [path] has through its use of [callee] at [at], or, for an
    [unsafe] block, through the block at [at]. *)
