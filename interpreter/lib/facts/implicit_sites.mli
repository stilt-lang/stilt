(** The operations of a body that can panic or allocate themselves, or that name
    items whose implicit effects they inherit (facts.inference and
    facts.allocation; effects.panic-kinds and effects.panicking-operations;
    facts.writes-in-place). *)

type site = {
  loc : Ast.loc;
  facts : (Ast.limit * string) list;
      (** The implicit effects the operation has itself, each with a message
          that says what it does, as in ["this list literal allocates"]. *)
  names : Implicit_names.key list;  (** The items it names. *)
  notes : (Ast.limit * string) list;
      (** For each effect it has that no rule of acceptance rules out, what the
          closest rule needs (facts.closest-rule). *)
}

val site :
  ?facts:(Ast.limit * string) list ->
  ?names:Implicit_names.key list ->
  ?notes:(Ast.limit * string) list ->
  Ast.loc ->
  site

val sites :
  ?proofs:Accept.t ->
  Env.t ->
  Implicit_in_place.result ->
  Tast.block ->
  site list
(** The sites of a body, closures included, in the order they are written. The
    writes that the in-place analysis of the body finds in place don't allocate,
    and the operations that the rules of acceptance prove don't panic
    (facts.range-loops, facts.guards, facts.divisors and facts.keys). *)

val no_in_place : Implicit_in_place.result
(** The in-place analysis of a body that writes nothing in place. *)

val names : Env.t -> Tast.block -> Implicit_names.key list
(** The items that the operations of a body name, closures included. *)
