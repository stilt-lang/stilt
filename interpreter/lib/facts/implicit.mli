(** Implicit effects (facts.implicit-effects; facts.div and facts.copy), and the
    checks of the [without] limits on them: [panic] (effects.without-panic),
    [alloc] (facts.without-alloc; facts.in-place-promise), [div]
    (facts.without-div) and [copy] (facts.without-copy). *)

type t
(** The implicit effects of a program's items, and the sites of their bodies. *)

val infer :
  Env.t -> Tast.program -> limited:(Ast.limit -> Tast.fn_def -> bool) -> t
(** The implicit effects of every item with a body. [limited l f] tells whether
    the body of [f] is limited by [l], through its module or its own clause:
    such a body counts as having no effect that [l] limits, and a body with an
    error as having none at all. The rules of acceptance read each body
    (facts.rules-of-acceptance): what they prove adds neither [panic] nor [div].
*)

val bodies : Tast.program -> (Implicit_names.key * Tast.fn_def) list
(** The functions and methods of a program, each with the key that names it. *)

val capabilities :
  Env.t -> Tast.program -> Implicit_names.key -> Ast.capability list
(** [capabilities env program] gives the capabilities of each item, in the order
    of facts.capabilities, as that rule and facts.capability-natives infer them
    from the items each body names, closures included. A [Broken] body, which
    has an error, has none. A key that names no item has none. *)

val limit_errors :
  Env.t ->
  t ->
  file:string ->
  limits:Ast.limit list ->
  key:Implicit_names.key option ->
  Tast.block ->
  Diagnostic.t list
(** The operations of a body that go beyond its [limits]: one error for each
    operation and limit it goes beyond, which says what the operation does, or
    which item it names has the effect. [key] is the item whose body it is, if
    it is one. *)

val lock_errors : Env.t -> t -> file:string -> Tast.block -> Diagnostic.t list
(** The E0430 of a body: each site of [locks] in the block of a [when], a [when]
    or a call of an item that has [locks], closure literals included, reported
    once (shared.locks). *)
