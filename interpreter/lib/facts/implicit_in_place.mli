(** Updates in place (facts.own-storage, facts.writes-in-place and
    facts.copy-at-call): which bindings of a body hold their own storage, which
    of its writes through an index are in place, and which arguments its calls
    copy for callees that update them in place. *)

type context = {
  env : Env.t;
  params : (Ast.mode * Hir.var) list;
  limited : bool;
      (** Whether the body's function is limited by [without alloc]. *)
  last : Modes_last.t;
  shared : Modes_shared.shared list;  (** The body's shared modifications. *)
  in_place : Implicit_names.key -> (int * Ast.mode) list;
      (** The in-place parameters of a callee, by their positions, a receiver
          first, with their modes. *)
}

type result = {
  writes : Tast.expr list;
      (** The places [b[i]] of a list [b], those that go on from [b[i]] through
          fields, tuple elements and elements of arrays when [b]'s elements
          aren't of a copy-on-write type, and the calls of [view.into] and
          [view.split], that write in place, so they don't allocate
          (facts.writes-in-place). *)
  copies : (Tast.expr * string) list;
      (** The arguments that a call copies for an in-place parameter, which
          allocate and copy (facts.copy-at-call and facts.copy), with why. *)
  reasons : (Tast.expr * string) list;
      (** Why each other such place, or call, isn't in place. *)
  reached : int list;
      (** The positions of the parameters whose storage reaches a write in place
          (facts.in-place-parameters). *)
}

val run : context -> Tast.block -> result
